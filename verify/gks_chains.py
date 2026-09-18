"""GKS/KRSW necklace-representative symmetric chain decomposition for prime n (KRSW Section 2)."""
from math import comb
def match(x):
    """parenthesis matching: '1' = right paren, '0' = left paren. Returns (unmatched0 positions, unmatched1 positions)."""
    stack=[]; un1=[]
    for i,ch in enumerate(x):
        if ch=='0': stack.append(i)
        else:
            if stack: stack.pop()
            else: un1.append(i)
    return stack, un1   # stack = unmatched 0s (in order)
def block_code(x):
    if x[0]=='0' or x[-1]=='1': return None
    code=[]; i=0; n=len(x)
    while i<n:
        a=0
        while i<n and x[i]=='1': a+=1; i+=1
        b=0
        while i<n and x[i]=='0': b+=1; i+=1
        code.append(a+b)
    return tuple(code)
def rotations(x): return [x[i:]+x[:i] for i in range(len(x))]
def is_rep(x):
    b=block_code(x)
    if b is None: return False
    return all(block_code(y) is None or b<=block_code(y) for y in rotations(x))
def nodes(n):
    out=[]
    for v in range(1,2**n-1):
        x=format(v,'0%db'%n)
        un0,un1=match(x)
        if len(un1)==1 and is_rep(x): out.append(x)
    return out
def parent(x):
    i=x.rindex('1'); return x[:i]+'0'+x[i+1:]
def chain(x):
    c=[x]
    while True:
        un0,_=match(c[-1])
        if len(un0)<=1: break
        i=un0[0]; y=c[-1][:i]+'1'+c[-1][i+1:]; c.append(y)
    return c
if __name__=='__main__':
    for n in (5,7,11,13,17):
        N=nodes(n); chains={x:chain(x) for x in N}
        covered=[y for c in chains.values() for y in c]
        assert len(covered)==len(set(covered))
        allreps=sum(1 for v in range(1,2**n-1) if is_rep(format(v,'0%db'%n))) if n<=13 else None
        print(n,'chains',len(N),'expected C(n,n//2)/n =',comb(n,n//2)//n,'elements covered',len(covered),'representatives',allreps,
              'parents in tree',all(parent(x) in chains or x=='1'+'0'*(n-1) for x in N))
        if n==7:
            for x in N: print('  C_'+x+':',' -> '.join(chains[x]))
