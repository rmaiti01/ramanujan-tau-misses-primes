1. ABC conjecture and Xiong's proposition 5.4 (label `\label{100}`) and other relevant results in `PRIME_VALUES_OF_RAMANUJAN_TAU_FUNCTION.tex` should be assumed whenever necessary. Here, "necessary" means if assuming them can greatly simplify the proof and avoid formalising deep results such as Siegel's theorem.

That is, formalizations need to dependend on ABC or proposition 5.4 whenever necessary:
```lean
def ABC : Prop := ...

def Proposition5_4 : Prop := ...

theorem some_theorem (h54 : Proposition5_4) (abc : ABC)  : ... := ...
```

2. When formalizing ramanujan's $\tau$ function, we use predicate instead of concrete definitions. That is, instead of defining $\tau$ via coefficients of power series, we will define $\tau$ by specifying a list of properties it should satisfy.

3. When using Xiong's proposition 5.4, use the strengthened version: 

Let $P = {\pm \ell : \ell \text{ odd prime}}$ and $X_{2k} = {\tau(p^{2k}) : p \text{ prime}}$. There exists $c_4 > 0$ such that for all $N > c_4$ and $3 \le k < \log N / (2 \log 2)$, 

$$#(P \cap X_{2k} \cap [-N, N]) \ll N^{1/2}.$$

There exists $c_5 > 0$ such that for all $N > c_5$ and $k \ge \log N / (2 \log 2)$, we have $X_{2k} \cap [-N, N] = \emptyset$.
