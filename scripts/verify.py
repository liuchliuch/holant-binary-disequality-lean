#!/usr/bin/env python3
"""Build, audit, replay and compare an exact source snapshot."""
import argparse
import datetime as dt
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys

from release import ROOT, closure, dependencies, digest, manifest, scan, write_axiom_audit


def snapshot_hash(files):
    return hashlib.sha256(json.dumps(files,sort_keys=True).encode()).hexdigest()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--trusted-local',action='store_true',help='Use trusted sources without an OS sandbox')
    parser.add_argument('--phase',choices=['all','build','kernel','comparator'],default='all',
                        help='CI phases share the exact Linux build artifact from this source snapshot')
    args=parser.parse_args()
    base=ROOT/'.lake/release';logs=base/args.phase;logs.mkdir(parents=True,exist_ok=True)
    output=base/'result.json' if args.phase=='all' else logs/'result.json'
    record={'status':'running','phase':args.phase,'started_utc':dt.datetime.now(dt.timezone.utc).isoformat(),
            'mode':'trusted-local' if args.trusted_local else 'linux-comparator-sandbox',
            'operating_system':platform.system(),'commit':os.environ.get('GITHUB_SHA'),'phases':[]}
    def save():output.write_text(json.dumps(record,indent=2)+'\n')
    def phase(name,argv,marker=None):
        print(name+': running',flush=True)
        log=logs/(name+'.log')
        with log.open('w') as f:
            proc=subprocess.Popen(argv,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
            while True:
                try:
                    code=proc.wait(timeout=60);break
                except subprocess.TimeoutExpired:
                    print(name+': still running; '+str(log.stat().st_size)+' log bytes',flush=True)
        text=log.read_text(errors='replace')
        failed=code!=0 or 'uncaught exception:' in text or 'leanchecker found a problem' in text
        if marker and marker not in text:failed=True
        record['phases'].append({'name':name,'status':'failed' if failed else 'passed',
                                 'exit_code':code,'log_sha256':digest(log)})
        save();print(name+': '+record['phases'][-1]['status'],flush=True)
        if failed:
            print(text[-12000:],file=sys.stderr)
            raise RuntimeError(name+' failed; inspect its artifact log')
        return text
    try:
        save();dependencies()
        if args.phase=='all':phase('manuscript-build',['bash','scripts/build_manuscript.sh'])
        record['source_scan']=scan()
        before=manifest();record['source_manifest_sha256']=snapshot_hash(before)
        (logs/'source-manifest.json').write_text(json.dumps(before,indent=2)+'\n')
        source=closure(['Holant'])
        lean_cache=ROOT/'.lake/build/lib/lean'
        phase('toolchain',['lean','--version'],'version 4.34.1')
        if args.phase in {'all','build'}:
            if args.phase=='build':
                shutil.rmtree(ROOT/'.lake/build',ignore_errors=True)
                record['clean_project_build']=True
            phase('build',['lake','build','Holant','Verification.Solution'])
            dependencies()
            audit=logs/'Axioms.lean';write_axiom_audit(audit)
            text=phase('axioms',['lake','env','lean','-j1','-M12000',str(audit)],'AXIOM AUDIT PASSED:')
            counts=re.search(r'AXIOM AUDIT PASSED: (\d+) modules; (\d+) declarations; (\d+) theorems',text)
            if not counts:raise RuntimeError('Missing axiom audit counts')
            record['axiom_audit']=dict(zip(['modules','declarations','theorems'],map(int,counts.groups())))
            objects={str(p.relative_to(ROOT/'.lake/build')):digest(p)
                     for p in (ROOT/'.lake/build').rglob('*') if p.is_file() and not p.name.endswith('.setup.json')}
            (logs/'object-sha256.json').write_text(json.dumps(objects,indent=2)+'\n')
            record['checked_object_manifest_sha256']=digest(logs/'object-sha256.json')
            phase('exact-errata',[sys.executable,'scripts/check_errata.py'])
            phase('pdf-integrity',['qpdf','--check','manuscript/paper.pdf'])
        else:
            build=json.loads((base/'build/result.json').read_text())
            if build['status']!='passed' or not build['clean_project_build']:
                raise RuntimeError('The clean library build has not passed')
            if build['source_manifest_sha256']!=record['source_manifest_sha256'] or build['commit']!=record['commit']:
                raise RuntimeError('Build artifact does not match this source snapshot and commit')
            object_manifest=base/'build/object-sha256.json'
            if digest(object_manifest)!=build['checked_object_manifest_sha256']:
                raise RuntimeError('Build object manifest changed')
            for name,expected in json.loads(object_manifest.read_text()).items():
                if digest(ROOT/'.lake/build'/name)!=expected:
                    raise RuntimeError('Build artifact changed: '+name)
            record['verified_build_artifact']=True
            record['build_object_manifest_sha256']=build['checked_object_manifest_sha256']
        if args.phase in {'all','kernel'}:
            phase('kernel-replay',['lake','env','leanchecker','--fresh','--verbose','Holant'],
                  'replaying Holant with --fresh')
            record['kernel_replay']={'mode':'fresh-environment','root':'Holant',
                                     'project_modules':len(source),'includes_imported_dependencies':True}
        if args.phase in {'all','comparator'}:
            mode=['--trusted-local'] if args.trusted_local else []
            phase('comparator',[sys.executable,'scripts/comparator.py',*mode],'Your solution is okay!')
            text=phase('comparator-negative-tests',[sys.executable,'scripts/comparator.py',*mode,'--negative-test'],
                      'COMPARATOR NEGATIVE TEST PASSED: extra-axiom')
            if text.count('COMPARATOR NEGATIVE TEST PASSED:')!=3:
                raise RuntimeError('Not all Comparator negative controls ran')
            record['comparator_theorems']=json.loads((ROOT/'Verification/comparator.json').read_text())['theorem_names']
            record['definition_holes']=0;record['negative_controls']=3
            record['process_isolation']='none' if args.trusted_local else 'Landrun with systemd AF_UNIX restriction'
            record['comparator_kernel_replay']='passed'
        dependencies()
        if before!=manifest():raise RuntimeError('Release source changed during verification')
        record.update(status='passed',source_unchanged=True,
                      allowed_axioms=['propext','Classical.choice','Quot.sound'],
                      manuscript_sha256=digest(ROOT/'manuscript/paper.pdf'))
    except Exception as error:
        record.update(status='failed',error=str(error));print(str(error),file=sys.stderr)
    finally:
        record['finished_utc']=dt.datetime.now(dt.timezone.utc).isoformat();save()
    return 0 if record['status']=='passed' else 1


if __name__=='__main__':sys.exit(main())
