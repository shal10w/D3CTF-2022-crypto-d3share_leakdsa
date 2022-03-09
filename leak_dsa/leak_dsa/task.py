from hashlib import sha256
from secret import flag
from Crypto.Util.number import *
from random import *
import os
from binascii import *
def gen_key(qbit , pbit):
    q = getPrime(qbit)
    while 1:
        p = getrandbits(pbit-qbit)*q + 1
        if isPrime(p):
            break
    while 1:
        h = randint(1 , p)
        g = pow(h , (p-1)//q , p)
        if g != 1:
            break
    d = randint(1 , q-1)
    y = pow(g,d,p)
    pubkey = (p ,q , g ,y)
    prikey = (p ,q ,g ,y , d)
    return pubkey , prikey

def sign(prikey , m):
    p,q,g,y,d = prikey
    k = randint(1 , q-1)
    r = pow(g , k , p) % q
    s = inverse(k , q) * (int(sha256(m).hexdigest(),16)+ d * r) % q
    return (r , s) , k
def verify(pubkey , m , r ,s ):
    p,q,g,y = pubkey
    w = inverse(s , q)
    u1 = int(sha256(m).hexdigest(),16) * w % q
    u2 = r * w % q
    if r == pow(g , u1 , p)*pow(y , u2,p)% q:
        return 1
    return 0
N = 70
pubkey , prikey = gen_key(256 , 2048)
f = open('./cipher.txt' , 'w')
f.write(str(pubkey) + '\n')
for i in range(N):
    m = os.urandom(10)
    signature , gift = sign(prikey , m)
    mask = getrandbits(256)
    f.write(hexlify(m).decode() + ',' + str(signature) +',' +str(mask & gift) +','+ str(mask) + '\n')

assert flag[:6] == b'd3ctf{' and flag[-1:] == b'}'
assert flag[6:-1] == sha256(str(prikey[-1]).encode()).hexdigest()
