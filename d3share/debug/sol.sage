#!sage
import random
from hashlib import sha256
from Crypto.Util.number import *


p = 2**48 - 59
r = 2**38
t = 40
n = 43
R = GF(p)
P = PolynomialRing(GF(p) , "x,y")
x , y = P.gens()
def L(X , xk , i):
    res = 1
    for j in range(len(X)):
        if j == i:
            continue
        res *= (xk - X[j]) / R(X[i] - X[j])
    return res
def lagrange_interpolation(X , fx , var = y):
    f = 0
    for i in range(t+1):
        prod = L(X[:t+1] , var , i)
        f += prod * fx[i]
    return f



# setup

def getdata():
    f = open('./d3share/debug/data.txt' , 'r')
    nodes = []
    for i in range(n):
        nodes.append(eval(f.readline()[:-1].replace('^' , '**')))
    return nodes
nodes = getdata()
hint = 35327434352315



# start attack

## get g - h

def getvec(nodes):
    X = [i[0] for i in nodes[:t+1]]
    x1 = nodes[t+1][0]
    fs = [i[1].coefficients() for i in nodes[:t+1]]
    v = nodes[t+1][1].coefficients()
    for i in range(t+1):
        prod = L(X , x1 , i)
        v = [(v[j] - prod * fs[i][j]) for j in range(t+1)]
    res = 0
    for i in range(t+1):
        res += v[i]*x^(t-i)
    return res

tempnodes = nodes[:t+2]
v1 = getvec(tempnodes)
X = [i[0] for i in tempnodes]

a = vector(GF(p) , [v1(i,0) for i in X])
A = Matrix(ZZ , a)
for i in range(len(X)):


    temp = [0]*len(X)
    temp[i] = p
    temp = vector(ZZ , temp)
    A = A.stack(temp)

g1 = A.BKZ(block_size = 22)[1]
k = a[0] * inverse(g1[0] , p) % p
gh = lagrange_interpolation(X[:t+1] , g1)
print(gh)

## distinguish g/h

def backpacker( c , K):
    n = len(K)
    M = Matrix(ZZ , n+2 , n+2)
    N = p

    for i in range(n):
        M[i+1,i] = 2
        M[n+1,i] = 1
        M[i+1,n] = int(K[i]) * N
    M[n+1,n] = int(c)*N
    M[0 , n] = int(p)*N
    M[n+1 , n+1] = 1
    print(M[n+1])
    res = M.BKZ(block_size = 22)[0]
    print(res)
    for i in res[:-2]:
        if abs(i) != 1:
            return 0
    return [(-res[-1]*res[i]+1)//2 for i in range(n)]

temp = [L(X[:t+1] , X[t+1] , i) for i in range(t+1)]
temp.append(-1)
res = backpacker(k , temp)
print(res)

## recover F

X = []
coefs = []
for i in range(t+2):
    tempx ,tempf = nodes[i]
    if res[i] == 1:
        tempf += gh
    X.append(tempx)
    coefs.append(tempf.coefficients())


F = 0
for i in range(t+1):
    fx = [coefs[j][i] for j in range(t+1)]
    F += y^(t-i)*lagrange_interpolation(X[:t+1] , fx[:t+1] , var = x)
F -= F(0 , y)
ycoef = F(x , 0).coefficients()
for i in range(t):
    F += ycoef[i]*y^(t-i)
F += hint
print(F)
flag = sha256(b''.join([long_to_bytes(int(i)) for i in F.coefficients()])).hexdigest()
print(flag)