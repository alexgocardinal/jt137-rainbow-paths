#!/usr/bin/env python3
"""Standalone exact verification of the 13-vertex JT 13.7 counterexample.
Requires Python stdlib and g++. No discovery code or SAT library is imported.
"""
import hashlib,itertools,json,subprocess,tempfile,time
from pathlib import Path
B=Path(__file__).resolve().parent;t=time.monotonic()
r=json.loads((B/'graph.json').read_text());n=r['n'];E=sorted(tuple(e) for e in r['edges']);arcs=sorted(tuple(e) for e in r['arcs'])
assert len(set(E))==len(E)==r['m'] and all(0<=a<b<n for a,b in E)
assert len(arcs)==len(set(arcs))==len(E)
assert sorted(tuple(sorted(e)) for e in arcs)==E
A=set(arcs);N=[set() for _ in range(n)]
for a,b in E:N[a].add(b);N[b].add(a)
# Independentlydecodegraph6, noNetworkXneeded.
g=r['graph6'];assert ord(g[0])-63==n
bits=[]
for c in g[1:]:bits.extend((ord(c)-63>>i)&1 for i in range(5,-1,-1))
at=0;decoded=[]
for v in range(1,n):
    for u in range(v):
        if bits[at]:decoded.append((u,v))
        at+=1
assert sorted(decoded)==E
P=[list(p) for p in itertools.permutations(range(n),4) if all(e in A for e in zip(p,p[1:]))]
assert P==r['directed4vertexpaths']
order=sorted(range(n),key=lambda v:(-len(N[v]),v));colors=[-1]*n
def count(q):
    R=[]
    def rec(i,mx):
        if i==n:R.append(colors[:]);return
        v=order[i];used={colors[u] for u in N[v]}
        for c in range(min(q,mx+2)):
            if c in used:continue
            colors[v]=c;rec(i+1,max(mx,c));colors[v]=-1
    rec(0,-1);return R
C3=count(3);C4=count(4);assert not C3 and len(C4)==1
assert all(len({c[v] for v in p})<4 for c in C4 for p in P)
assert all(r['color4'][a]!=r['color4'][b] for a,b in E)
# A short human path proof: every possible middle arc is one of nine cases.
M=json.loads((B/'midpoint_certificate.json').read_text());derived=[]
for u,v in arcs:
    predecessors=sorted(x for x,a in arcs if a==u)
    successors=sorted(y for b,y in arcs if b==v)
    paths=[(x,u,v,y) for x in predecessors for y in successors if len({x,u,v,y})==4]
    if not paths:continue
    patterns=sorted({tuple(r['color4'][z] for z in p) for p in paths})
    assert all(len(set(pattern))<4 for pattern in patterns)
    derived.append({'middle_arc':[u,v],'predecessors':predecessors,'successors':successors,'color_patterns':[list(p) for p in patterns],'path_count':len(paths)})
assert M==derived and len(M)==9 and sum(c['path_count'] for c in M)==len(P)
# Tinyhumanproofcertificate: threefailingbranches andonefullyforcedcoloring.
F=json.loads((B/'uniqueness_forcing_tree.json').read_text())
anchor=F['triangle_anchor'];assert len(anchor)==3
assert all(tuple(sorted(e)) in E for e in itertools.combinations(anchor,2))
leaf_count=0;conflict_count=0
def check_tree(node,assigned):
    global leaf_count,conflict_count
    assigned=dict(assigned)
    for v,c in node['forced']:
        assert v not in assigned
        forbidden={assigned[u] for u in N[v] if u in assigned}
        # Allthreeothercolorsareblocked; blockingcalsoisanimmediate
        # contradiction, subsequently checkedbytheexplicitconflictedge.
        assert set(range(4))-{c} <= forbidden;assigned[v]=c
    if 'conflict' in node:
        a,b,c=node['conflict'];assert b in N[a] and assigned[a]==assigned[b]==c
        conflict_count+=1;return
    if 'solution' in node:
        assert len(assigned)==n
        solution=[assigned[v] for v in range(n)]
        assert solution==node['solution']==r['color4']
        assert all(solution[a]!=solution[b] for a,b in E)
        leaf_count+=1;return
    v=node['branch_vertex'];assert v not in assigned
    available=set(range(4))-{assigned[u] for u in N[v] if u in assigned}
    assert sorted(available)==node['branch_colors']
    assert sorted(branch['color'] for branch in node['branches'])==sorted(available)
    for branch in node['branches']:
        child=dict(assigned);child[v]=branch['color'];check_tree(branch['child'],child)
check_tree(F['tree'],dict(zip(anchor,F['anchor_colors'])))
assert leaf_count==1 and conflict_count==3
def cnf(q):
    C=[]
    for v in range(n):
        C.append([v*q+c+1 for c in range(q)])
        C.extend([[-(v*q+a+1),-(v*q+b+1)] for a,b in itertools.combinations(range(q),2)])
    C.extend([[-(a*q+c+1),-(b*q+c+1)] for a,b in E for c in range(q)])
    return C
catalogue=json.loads((B/'proof_catalogue.json').read_text());additions=0
with tempfile.TemporaryDirectory() as td:
    exe=Path(td)/'rup';subprocess.run(['g++','-O2','-std=c++17',str(B/'check_rup.cpp'),'-o',str(exe)],check=True)
    for c in catalogue:
        name=c['name'];q=c['q'];C=cnf(q)
        if name.startswith('path'):
            j=int(name[4:7]);C+=[[v*4+i+1] for i,v in enumerate(P[j])]
        elif name=='unique4coloring_trianglefixed':
            C+=[[v*4+i+1] for i,v in enumerate(r['triangle_anchor'])]
            C+=[[-(v*4+r['color4'][v]+1) for v in range(n)]]
        else:assert name=='non3colorable'
        text=f'p cnf {n*q} {len(C)}\n'+''.join(' '.join(map(str,x))+' 0\n' for x in C)
        cp=B/(name+'.cnf');pp=B/(name+'.drup')
        assert cp.read_text()==text
        assert hashlib.sha256(cp.read_bytes()).hexdigest()==c['cnf_sha256']
        assert hashlib.sha256(pp.read_bytes()).hexdigest()==c['proof_sha256']
        s=subprocess.run([str(exe),str(cp),str(pp)],capture_output=True,text=True);assert s.returncode==0,(name,s.stderr)
        additions+=int(s.stdout.split()[1])
    bad=Path(td)/'empty.drup';bad.write_text('')
    s=subprocess.run([str(exe),str(B/'non3colorable.cnf'),str(bad)],capture_output=True,text=True);assert s.returncode!=0
print(json.dumps({'status':'PASS','n':n,'m':len(E),'proper3colorings_mod_renaming':len(C3),'proper4colorings_mod_renaming':len(C4),'directed4vertexpaths':len(P),'rainbow4vertexpaths':0,'middle_arc_cases':len(M),'rup_proofs':len(catalogue),'rup_additions':additions,'seconds':time.monotonic()-t,'scope':'Exact finite counterexample to JT 13.7; publication priority and current status are separate.'}))
