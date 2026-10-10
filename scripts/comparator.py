#!/usr/bin/env python3
"""Build pinned upstream Comparator tools and verify the public statements."""
import argparse
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess

from release import ROOT, dependencies, digest, manifest
from sandbox_check import check as check_sandbox, guard


def run(args, cwd=ROOT, env=None):
    subprocess.run(list(map(str,args)),cwd=cwd,env=env,check=True)


def checkout(spec, destination):
    if not destination.exists():
        run(['git','clone','--no-checkout',spec['url'],destination])
        run(['git','checkout','--detach',spec['revision']],cwd=destination)
    actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=destination,text=True).strip()
    if actual!=spec['revision']: raise RuntimeError('Unexpected tool revision: '+destination.name)
    origin=subprocess.check_output(['git','remote','get-url','origin'],cwd=destination,text=True).strip()
    if origin!=spec['url']: raise RuntimeError('Unexpected tool origin: '+destination.name)
    run(['git','diff','--quiet','HEAD'],cwd=destination)


def setup(trusted_local):
    lock=json.loads((ROOT/'Verification/tools.json').read_text())
    base=ROOT/'.tools';base.mkdir(exist_ok=True)
    comparator=base/'comparator'
    checkout(lock['comparator'],comparator)
    toolchain=(ROOT/'lean-toolchain').read_text().strip()
    run(['lake','+'+toolchain,'build','comparator','lean4export'],cwd=comparator)
    exporter=comparator/'.lake/packages/lean4export'
    actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=exporter,text=True).strip()
    if actual!=lock['lean4export']['revision']: raise RuntimeError('Unexpected exporter revision')
    run(['git','diff','--quiet','HEAD'],cwd=exporter)
    env=os.environ.copy()
    env['COMPARATOR_LEAN4EXPORT']=str(exporter/'.lake/build/bin/lean4export')
    if trusted_local:
        env['COMPARATOR_LANDRUN']=str(comparator/'scripts/fake-landrun.sh')
        print('MODE: trusted local sources; no operating-system sandbox',flush=True)
    else:
        if platform.system()!='Linux':
            raise RuntimeError('Sandboxed verification requires Linux; trusted sources may use --trusted-local')
        landrun=base/'landrun'
        checkout(lock['landrun'],landrun)
        run(['go','build','-o','landrun','./cmd/landrun'],cwd=landrun)
        env['LANDRUN_EXECUTABLE']=str(landrun/'landrun')
        env['COMPARATOR_LANDRUN']=str(ROOT/'scripts/landrun-runner.sh')
        check_sandbox(landrun/'landrun')
    return comparator/'.lake/build/bin/comparator',env


def invocation(binary, config, trusted_local):
    cmd=['lake','env',str(binary),str(config)]
    if not trusted_local:
        cmd=guard()+['-E','PATH', '-E','LEAN_NUM_THREADS', '-E','LANDRUN_EXECUTABLE',
             '-E','COMPARATOR_LANDRUN','-E','COMPARATOR_LEAN4EXPORT',
             '--working-directory='+str(ROOT),'--',*cmd]
    return cmd


def negative_test(binary, env, trusted_local):
    """Reject changed statements and extra axioms for the intended statement."""
    source=ROOT/'Verification/ComparatorMismatch.lean'
    cfg=ROOT/'.lake/release/comparator-mismatch.json'
    if source.exists(): raise RuntimeError('Refusing to replace an existing mismatch fixture')
    cfg.parent.mkdir(parents=True,exist_ok=True)
    header=('import Holant.Statements\nnamespace Holant.Theorems\nopen Holant.Tractable\n'
            'variable {s : Nat} {a : Nat → Nat}\n'
            'variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))\n')
    cases=[
        ('different-statement', 'theorem binaryDisequality : True := trivial\n',
         "Challenge and solution theorem statement do not match: 'Holant.Theorems.binaryDisequality'"),
        ('added-premise', 'theorem binaryDisequality (h : False) : Statements.BinaryDisequality G := False.elim h\n',
         "Challenge and solution theorem statement do not match: 'Holant.Theorems.binaryDisequality'"),
        ('extra-axiom', 'axiom extraProof : Statements.BinaryDisequality G\n'
         'theorem binaryDisequality : Statements.BinaryDisequality G := extraProof G\n',
         'Holant.Theorems.extraProof')]
    conf=json.loads((ROOT/'Verification/comparator.json').read_text())
    conf['solution_module']='Verification.ComparatorMismatch'
    conf['theorem_names']=['Holant.Theorems.binaryDisequality']
    cfg.write_text(json.dumps(conf,indent=2)+'\n')
    try:
        for label, body, rejection in cases:
            source.write_text(header+body+'end Holant.Theorems\n')
            result=subprocess.run(invocation(binary,cfg,trusted_local),cwd=ROOT,env=env,
                                  stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            (ROOT/'.lake/release'/('comparator-'+label+'.log')).write_text(result.stdout)
            if result.returncode==0 or rejection not in result.stdout:
                raise RuntimeError('Expected Comparator rejection missing: '+label)
            if label=='extra-axiom' and 'axiom' not in result.stdout.lower():
                raise RuntimeError('Extra axiom was not rejected by the axiom check')
            print('COMPARATOR NEGATIVE TEST PASSED: '+label,flush=True)
    finally:
        source.unlink()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--trusted-local',action='store_true',help='Use the upstream development shim for already trusted local sources')
    parser.add_argument('--setup-only',action='store_true')
    parser.add_argument('--negative-test',action='store_true')
    args=parser.parse_args()
    dependencies()
    before=manifest()
    binary,env=setup(args.trusted_local)
    binaries=[binary, Path(env['COMPARATOR_LEAN4EXPORT'])]
    if not args.trusted_local:binaries.append(Path(env['LANDRUN_EXECUTABLE']))
    hashes={str(p):digest(p) for p in binaries}
    if args.setup_only:return
    if args.negative_test:
        negative_test(binary,env,args.trusted_local)
    else:
        run(invocation(binary,ROOT/'Verification/comparator.json',args.trusted_local),env=env)
    dependencies()
    if before!=manifest():raise RuntimeError('Source changed during comparison')
    if hashes!={str(p):digest(p) for p in binaries}:raise RuntimeError('Verification binary changed')


if __name__=='__main__':main()
