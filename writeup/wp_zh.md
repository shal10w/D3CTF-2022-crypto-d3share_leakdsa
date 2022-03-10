### d3share

背景

题目实现了一个基于扰动多项式的协议，每个node通过自己的私钥与他人的公钥就能够不通过交互，与其他node共享一个共享秘密，但他无法计算出其他node之间的共享秘密。但如果一个攻击者得到了足够多node的私钥，则他能够计算出任意两个node之间的共享秘密，本题要求就是通过t+3个node计算出完整的F(实际上只需要t+2，出题人绕了一点点弯路，导致多给了一个)

预期解

（开头有一个小技巧，如果直接通过题目脚本生成测试数据会非常慢，可以通过拉格朗日插值先自己选t+1个点得到g和h，再枚举2个点会极大加快速度，方便调试）

文献《Attacking Cryptographic Schemes Based on “Perturbation Polynomials”》中提出了利用Lattice的攻击方式

$F(x,y) = \sum_{i=0}^tf_i(x)y^i$，设$\pmb{F_i} = (f_0(x_i) , f_1(x_i) , ... f_t(x_i))$

则每个node的私钥$\pmb{p_i} = \pmb{F_i} + b_i\pmb{g} + (1-b_i)\pmb{h}$

其中$\pmb{g},\pmb{h}$为g和h的系数向量

设
$$
L(X , x , i) = \prod_{j\ne i}\frac{x - X_j}{X_i - X_j}\tag{1}
$$
由拉格朗日插值公式
$$
P(x) = \sum_{i=0}^tP(x_i)L(X , x , i)\tag{2}
$$
对t+2个node的私钥使用该式可得
$$
\pmb{p_{t+1}}-\sum_{i=0}^t\pmb{p_i}L(X , x_{t+1} , i) =(b_{t+1} - \sum_{i=0}^t L(X , x , i)b_i)\pmb{g} + ((1-b_{t+1}) - \sum_{i=0}^t L(X , x , i)(1-b_i))\pmb{h}\tag{3}
$$
论文中讨论的是g与h系数独立的情况，从而能够通过上式得到g与h的一个线性组合，对第t+2个node运用上式，大概率能够得到与先前线性无关的另一个线性组合，从而通过LLL算法得到g与h。而题目中，g与h的系数相加恒为1,这导致了g与h的系数向量永远线性相关。

原因是
$$
(b_{t+1} - \sum_{i=0}^t L(X , x , i)b_i) + ((1-b_{t+1}) - \sum_{i=0}^t L(X , x , i)(1-b_i)) = 1 - \sum_{i=0}^t L(X , x , i)\tag{4}
$$
在(2)式中，我们知道L返回的是一个t次多项式，则$P(x) - 1$也是一个t次多项式，一个t次多项式若有t+1个不同的根，则该多项式恒为0,因此当$P(x_i) = 1$时，有
$$
P(x) =\sum_{i = 0}^tL(X,x,i) = 1
$$
所以(4)式右边恒为0，即g与h的系数互为相反数，因此得到的永远是k(g - h)

但由于(g-h)(x_i)很小，我们可以通过LLL算法，通过k(g-h)得到g-h，与k

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

由于得不到g与h，因此无法通过论文所提的方法继续求解F，但可以注意到(3)式中，g的系数从上一步中得到，系数已知，则我们可以将求解b_i的问题转化为一个子集和问题。（按照原始论文给出的参数，p = 2\^32-5,t = 70的情况下，背包重量过大无法求解，因此我将p适当增大，t减小了一些，将背包重量减小至0.8左右，从而使其能够求解）

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



接下来就可以将所有的f+h转化为f+g，可以使用拉格朗日插值计算出f_i(x)的非常数项

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



对于i != 0时f_i(x)的常数系数可以通过F的对称性求得，i = 0时的常数无法求解(其实对于攻破系统来说是不需要求解的，只需要随便枚举一个g(x_i)就能够求解出一个常数项，该常数与真正的常数差距小于r，此时已经能够得到任意两个node的shared secret)，题目给出了hint = F(0,0)，因此可以完全恢复出F，计算flag

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

非预期（Nu1L）：

Nu1L的选手给出了一个非常漂亮的分辨g与h的方法

对于任意三个node i, j, k，若他们对应的b_i = b_j = b_k，不妨设b_i = 1则
$$
(p_i(x_j) - p_j(x_i))+(p_j(x_k) - p_k(x_j)) + (p_k(x_i) - p_i(x_k)) = g(x_j) - g(x_i) + g(x_k) - g(x_j) + g(x_i) - g(x_k) = 0
$$
若其中某个不等，不妨设b_i = b_j = 1, b_k = 0
$$
(p_i(x_j) - p_j(x_i))+(p_j(x_k) - p_k(x_j)) + (p_k(x_i) - p_i(x_k)) = g(x_j) - g(x_i) + g(x_k) - h(x_j) + h(x_i) - g(x_k) \ne 0
$$
因此经过简单的枚举（假设b_0 = b_1，概率为1/2,若结果不对则假设b_0 = b_2以此类推，第i个还不对的概率是2^-i）可以不通过格与拉格朗日插值分辨出g与h。

分辨出g与h后，与预期解最后一步相同的方式即可解出flag。

### leak_dsa

题目是一个标准的dsa，但泄露了k&mask的值，也就是泄露了k不连续的一些bit，将每一段连续的未知值设为$k_i$(上界为$2^{K_i}$)，可以得到
$$
k = k\&mask + \sum_i^tk_i*2^{m_i}
$$
将每个k_i都看做一个未知数，则k可以表示为一个多项式，我们希望这个多项式通过简单的变换能够有一个较小的上界，这样就能够将问题转化为普通的已知msb的hnp问题了。因此我们可以使用coppersmith的思路，构造一个格
$$
M = \left[
\begin{matrix}
p*2^{K_0} & 0&\cdots & 0\\
0 & p*2^{K_1}&\cdots & 0\\
\vdots&\vdots&\ddots & p*2^{K_t}\\
2^{m_0}*2^{K_0}&2^{m_1}*2^{K_1}&\cdots&2^{m_t}*2^{K_t}

\end{matrix}
\right]
$$
对M使用LLL算法后可以得到较小向量$v$，以此为系数的多项式的上界是比较小的，计算1-范式后得到大多数大约为251bit左右，相当于5bit的msb leak。有一些mask会更多。

计算

```python
g = (M.LLL()[0,0]//2**K0)*inverse_mod(2**k0 , q) % q
```

回到dsa等式中
$$
k = m/s+dr/s\\
dr/s + m/s - k\&mask =\sum_i^tk_i*2^{m_i}\\
g*(dr/s + m/s - k\&mask) = g*\sum_i^tk_i*2^{m_i} \le ||v||_1
$$
至此，题目化为普通的hnp问题，容易解出。

