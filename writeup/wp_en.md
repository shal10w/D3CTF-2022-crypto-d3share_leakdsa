## d3share

### background

the challenge implements a key predistribution scheme based on random perturbation. Every node can share secret with each other by their private key and the other's public key. But he can't compute the secret shared between other two nodes.  If an attacker get enough private key, then he will be able to compute the secret shared between any nodes. This challenge is to compute the F by t+3 nodes.(in fact , we only need t+2 nodes)

### expected solution

(A little trick at the beginning. if you try to generate the test data directly through the task.sage, it will be very slow. you can choose t+1 points and use lagrange interpolation formula to get g and h. then enumerate the left two points. It will greatly speed up and facilitate debugging)

the papre 《Attacking Cryptographic Schemes Based on “Perturbation Polynomials”》 proposed an attack using Lattice.

$F(x,y) = \sum_{i=0}^tf_i(x)y^i$，let $\pmb{F_i} = (f_0(x_i) , f_1(x_i) , ... f_t(x_i))$

then for every node's we have $\pmb{p_i} = \pmb{F_i} + b_i\pmb{g} + (1-b_i)\pmb{h}$

the $\pmb{g},\pmb{h}$ in it are the coefficient vector of g and h.

let 
$$
L(X , x , i) = \prod_{j\ne i}\frac{x - X_j}{X_i - X_j}\tag{1}
$$
recall the lagrange interpolation formula
$$
P(x) = \sum_{i=0}^tP(x_i)L(X , x , i)\tag{2}
$$
apply (2) to the private key of t+2 nodes and we can get 
$$
\pmb{p_{t+1}}-\sum_{i=0}^t\pmb{p_i}L(X , x_{t+1} , i) =(b_{t+1} - \sum_{i=0}^t L(X , x , i)b_i)\pmb{g} + ((1-b_{t+1}) - \sum_{i=0}^t L(X , x , i)(1-b_i))\pmb{h}\tag{3}
$$
the paper discusses the case where the coefficients of g and h are independent.Thus, a linear combination of g and h can be obtained through the above formula, and by applying the above formula to the t+2th node, another linear combination that is independent of the previous linearity can be obtained with high probability. So he can compute g and h by LLL. But here, the coefficients of g and h always add up to 0. This results in the coefficient vector of g and h being always linearly related.

the reason is 
$$
(b_{t+1} - \sum_{i=0}^t L(X , x , i)b_i) + ((1-b_{t+1}) - \sum_{i=0}^t L(X , x , i)(1-b_i)) = 1 - \sum_{i=0}^t L(X , x , i)\tag{4}
$$
in the formula (2), we know L returns a polynomial of degree t. So $P(x) - 1$ is also a polynomial of degree t. If a polynomial of degree t has t+1 different roots, this polynomial is 0. So when $P(x_i) = 1$, we have
$$
P(x) =\sum_{i = 0}^tL(X,x,i) = 1
$$
So the right hand side of formula (4) is always 0 and we always get k(g - h).

Because (g - h)(x_i) is small (< r), so we can use LLL to get (g - h) and k.

```python
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
print(k)
```

Since g and h are not available, it is impossible to continue to solve F by the method proposed in the paper. But we noticed that in formula (3), k is the coefficient of g, so we can convert the problem of solving b_i into a subset sum problem.(unfortunately, it can only used to solve this ctf challenge. According to the parameters given in the original scheme, p = 2^32 - 5 and t = 70, the weight is larger than 1 and is still difficult to solve. I increased p and decreased t to reducing the knapsack weight to around 0.8, allowing it to solve.)

```python
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
```

Then we can convert every f+h to f + g by our g - h. And use lagrange interpolation to get the non-constant coefficients of f_i(x)

```python
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
```

For i != 0, the constant coefficient of f_i(x) can be obtained by the symmetry of F. when i = 0, the constant coefficient can't be solved. But we can get it from the hint = F(0 , 0). So now we can fully recover F and get the flag.

```python
F -= F(0 , y)
ycoef = F(x , 0).coefficients()
for i in range(t):
    F += ycoef[i]*y^(t-i)
F += hint
print(F)
flag = sha256(b''.join([long_to_bytes(int(i)) for i in F.coefficients()])).hexdigest()
print(flag)
```

In fact, if we only want to break this scheme, the constant coefficient of F is unnecessary. randomly choose a g(x_0) < r, we can compute a number close to the constant coefficient and the difference is less than r. It's enough to compute the secret between every two nodes.

### unexpected solution by Nu1L:

Nu1L gives a very clever way to distinguish g and h.

For any 3 nodes i , j , k, if b_i = b_j = b_k = 1
$$
(p_i(x_j) - p_j(x_i))+(p_j(x_k) - p_k(x_j)) + (p_k(x_i) - p_i(x_k)) = g(x_j) - g(x_i) + g(x_k) - g(x_j) + g(x_i) - g(x_k) = 0
$$
if one of them is not 1，let b_i = b_j = 1, b_k = 0
$$
(p_i(x_j) - p_j(x_i))+(p_j(x_k) - p_k(x_j)) + (p_k(x_i) - p_i(x_k)) = g(x_j) - g(x_i) + g(x_k) - h(x_j) + h(x_i) - g(x_k) \ne 0
$$
so we can assume b_0 = b_1(if not , try b_2 and so on).and use the above method to distinguish g and h. The last step is the same as the expected solution

## leak_dsa

this challenge implements a standard dsa but leaked k&mask. so we can know some bits of k. but these bits are discrete and splits the k to many small k_i.
$$
k = k\&mask + \sum_i^tk_i*2^{m_i}
$$
we want k has a small upper bound so that we can convert the problem to a normal hnp. To achieve this, we can use a method similar to coppersmith's idea.

Construct a Lattice like
$$
M = \left[
\begin{matrix}
q*2^{K_0} & 0&\cdots & 0\\
0 & q*2^{K_1}&\cdots & 0\\
\vdots&\vdots&\ddots & q*2^{K_t}\\
2^{m_0}*2^{K_0}&2^{m_1}*2^{K_1}&\cdots&2^{m_t}*2^{K_t}

\end{matrix}
\right]
$$
apply LLL to M, we can get a short vector v. and in our experiments, we compute the 1-norm of v, it's often about 251 bits.

compute

```python
g = (M.LLL()[0,0]//2**K0)*inverse_mod(2**k0 , q) % q
```

and return to the formula of dsa.


$$
k = m/s+dr/s\\
dr/s + m/s - k\&mask =\sum_i^tk_i*2^{m_i}\\
g*(dr/s + m/s - k\&mask) = g*\sum_i^tk_i*2^{m_i} \le ||v||_1 
$$
now, we can convert the problem to a easy hnp and solve it with LLL or BKZ.







  









