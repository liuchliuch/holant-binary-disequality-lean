#!/usr/bin/env python3
"""Reproducible source, dependency, axiom and archive checks (Python standard library)."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parent.parent
ALLOWED_AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']
ENTRY_POINTS = ['Holant', 'Verification.Challenge', 'Verification.Solution']
OMIT = {'.lake', '.git', '.tools', '__pycache__', '.DS_Store'}


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            h.update(block)
    return h.hexdigest()


def uncomment(text):
    """Remove nested Lean comments, preserving strings and line breaks."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        pair, char = text[i:i+2], text[i]
        if depth:
            if pair == '/-': depth += 1; i += 2; continue
            if pair == '-/': depth -= 1; i += 2; continue
            out.append('\n' if char == '\n' else ' ')
        elif quoted:
            out.append(char)
            if char == '\\' and i+1 < len(text):
                out.append(text[i+1]); i += 2; continue
            if char == '"': quoted = False
        elif pair == '/-': depth = 1; i += 2; out.append(' '); continue
        elif pair == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
            continue
        else:
            out.append(char)
            if char == '"': quoted = True
        i += 1
    if depth: raise ValueError('Unterminated Lean comment')
    return ''.join(out)


def imports(path):
    result = []
    for raw in uncomment(path.read_text()).splitlines():
        line = raw.strip()
        if not line or line in ('module', 'prelude'): continue
        match = re.fullmatch(r'(?:public\s+)?import\s+(.+)', line)
        if not match: break
        result.extend(match.group(1).split())
    return result


def closure(roots):
    found, active = {}, set()
    def visit(name):
        if name in active: raise ValueError('Import cycle: '+name)
        if name in found: return
        file = ROOT/(name.replace('.', '/')+'.lean')
        if not file.is_file():
            if name == 'Holant' or name.startswith(('Holant.', 'Verification.')):
                raise ValueError('Missing project import: '+name)
            return
        active.add(name)
        found[name] = {'sha256': digest(file), 'imports': imports(file)}
        for child in found[name]['imports']: visit(child)
        active.remove(name)
    for root in roots: visit(root)
    return found


def dependencies():
    manifest = json.loads((ROOT/'lake-manifest.json').read_text())
    for pkg in manifest['packages']:
        path = ROOT/'.lake/packages'/pkg['name']
        if not path.exists(): continue  # Lake fetches the locked revision on first build.
        for argv, expected in [(['remote','get-url','origin'],pkg['url']),
                               (['rev-parse','HEAD'],pkg['rev'])]:
            actual = subprocess.check_output(['git','-C',str(path),*argv],text=True).strip()
            if actual != expected:
                raise ValueError('Pinned dependency mismatch: '+pkg['name'])
        subprocess.run(['git','-C',str(path),'diff','--quiet','HEAD'],check=True)


def release_files():
    files = []
    for directory, dirs, names in os.walk(ROOT):
        dirs[:] = sorted(d for d in dirs if d not in OMIT)
        for name in sorted(names):
            if name in OMIT: continue
            f = Path(directory)/name
            if f.is_symlink(): raise ValueError('Release symlink: '+str(f))
            files.append(f)
    return files


def scan():
    graph = closure(ENTRY_POINTS)
    all_modules = {str(p.relative_to(ROOT).with_suffix('')).replace('/','.')
                   for d in ['Holant','Verification'] for p in (ROOT/d).rglob('*.lean')}
    all_modules.add('Holant')
    if all_modules != set(graph):
        raise ValueError('Unreachable source files: '+str(sorted(all_modules-set(graph))))
    for name in graph:
        text = (ROOT/(name.replace('.','/')+'.lean')).read_text()
        code = re.sub(r'"(?:\\.|[^"\\])*"','""',uncomment(text))
        banned = re.findall(r'\b(?:sorry|admit|axiom|native_decide|ofReduceBool|trustCompiler)\b',code)
        if name == 'Verification.Challenge':
            if banned != ['sorry']*4: raise ValueError('Unexpected challenge holes')
        elif banned: raise ValueError('Forbidden proof construct in '+name+': '+str(banned))
        if name.startswith('Holant') and 'Verification.' in code:
            raise ValueError('Proof library imports a verification environment: '+name)
    trusted = closure(['Holant.Statements'])
    forbidden = ['Holant.Proofs','Holant.Library','Holant.Decidability']
    forbidden += [n for n in trusted if n.startswith('Holant.Proofs.Dichotomy.')]
    if set(trusted)&set(forbidden):
        raise ValueError('Statement boundary includes main proof assembly')
    for f in release_files():
        rel = f.relative_to(ROOT).as_posix()
        if f.suffix in {'.lean','.py','.sh','.md','.json','.toml','.yml','.yaml','.tex','.bib','.cff','.txt'} or f.name in {'LICENSE','NOTICE','lean-toolchain','.gitignore','.gitattributes'}:
            text = f.read_text()
            if re.search('[\u3400-\u9fff]',text): raise ValueError('Non-English prose in '+rel)
            if re.search(r'/[U]sers/|/[h]ome/[^/\s]+/|/[t]mp/|BEGIN (?:RSA |OPENSSH |EC )?PRIVATE KEY|ghp_[A-Za-z0-9]{20}|sk-[A-Za-z0-9]{32}',text):
                raise ValueError('Local path or credential-like text in '+rel)
        if f.suffix in {'.olean','.ilean','.trace','.log','.aux','.out','.toc','.blg','.fls','.fdb_latexmk','.pyc'}:
            raise ValueError('Build artifact in release: '+rel)
    return {'project_modules':len(graph),'proof_modules':len(closure(['Holant'])),
            'statement_modules':len(trusted),'allowed_axioms':ALLOWED_AXIOMS,
            'challenge_holes':4,'unreachable_modules':0,'english_only':True}


def write_axiom_audit(path):
    graph = closure(['Holant'])
    names = ',\n'.join('    `'+n for n in sorted(graph))
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text('''import Holant
import Lean.Util.CollectAxioms
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let expected : Array Name := #[
'''+names+''']
  let actual := env.header.moduleNames.filter fun n => (`Holant).isPrefixOf n
  unless actual.size == expected.size do
    throwError "Project import count mismatch"
  for n in expected do
    unless actual.contains n do throwError "Missing project module {n}"
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      if (`Holant).isPrefixOf env.header.moduleNames[idx.toNat]! then
        declarations := declarations + 1
        if info.isTheorem then theorems := theorems + 1
        for ax in (← collectAxioms name) do
          unless allowed.contains ax do throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"AXIOM AUDIT PASSED: {actual.size} modules; {declarations} declarations; {theorems} theorems"
''')


def manifest():
    return {str(p.relative_to(ROOT)):digest(p) for p in release_files()
            if p.relative_to(ROOT).as_posix() not in {'Verification/result.json','Verification/SHA256SUMS'}}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=['dependencies','scan','axioms','manifest','package'])
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    if args.command=='dependencies': dependencies()
    elif args.command=='scan': print(json.dumps(scan(),indent=2))
    elif args.command=='axioms': write_axiom_audit(args.output or ROOT/'.lake/release/Axioms.lean')
    elif args.command=='manifest':
        out=args.output or ROOT/'.lake/release/source-manifest.json'
        out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(manifest(),indent=2)+'\n')
    elif args.command=='package':
        scan()
        record=json.loads((ROOT/'.lake/release/result.json').read_text())
        if record.get('status')!='passed': raise ValueError('Release verification has not passed')
        current=manifest()
        if record['source_manifest_sha256']!=hashlib.sha256(json.dumps(current,sort_keys=True).encode()).hexdigest():
            raise ValueError('Release sources changed after verification')
        if args.output is None: raise ValueError('--output is required')
        destination=args.output.resolve()
        if destination.is_relative_to(ROOT): raise ValueError('Archive must be outside the repository')
        with zipfile.ZipFile(destination,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
            for f in release_files():
                info=zipfile.ZipInfo('holant-binary-disequality-lean/'+f.relative_to(ROOT).as_posix(),(2026,10,10,0,0,0))
                info.create_system=3
                info.compress_type=zipfile.ZIP_DEFLATED
                info.external_attr=(0o100755 if f.suffix=='.sh' else 0o100644)<<16
                z.writestr(info,f.read_bytes(),compresslevel=9)
        with zipfile.ZipFile(destination) as z:
            if z.testzip() is not None: raise ValueError('Archive integrity failure')
        print(json.dumps({'archive':str(destination),'bytes':destination.stat().st_size,'sha256':digest(destination),'files':len(release_files())},indent=2))


if __name__=='__main__':
    main()
