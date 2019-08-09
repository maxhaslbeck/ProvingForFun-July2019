

# Summary of JULY 2019 Contest:

This documents contains a Summary of the July 2019 Contest at "Proving for Fun"


## Cronology:


* 2019-07-05 17:13 - Contest starts with 4+1 Tasks and support for Isabelle and Coq
* After 3 hours - *eberlm* submits first overall solution for task **Special Pythagorean Triple** in Isabelle
* Shortly after - *eberlm* submits first overall solution for task **Fun modulo 5** in Isabelle
* Shortly after - *Azael* solves **Special Pythagorean Triple** and **Fun modulo 5** in Coq
* 5 hours into the contest - *eberlm* submits first correct solution for task **A Funky Grammar** in Isabelle
* 23 hours into the contest - *eberlm* submits the first correct solution for **XOR** in Isabelle, and thus has solved all 4 *solvable* tasks.
* Day 3 - *jonathye* submits the first Coq solution for **XOR** and later the same day the first Coq solution for **A Funky Grammar**, and thus is second to solve all *solvable* tasks
* Day 5 - the user named *j* has solved all four tasks in Coq
* 
* Day 9 - *tahasaf* has solved all four tasks in Isabelle, as well as *Nitrate* did in Coq
* Day 13 - *lasydler* solved all 4 tasks in Coq
* Day 26 - *s-quark* and *aleksey* did all 4 tasks in Coq
* Day 26 - ACL2 and Lean enter the competition and *alexjbest* is the first to trick the system by solving **break the system** for Coq. Subsequently the loophole is closed, but the point is still valid to *alexjbest* and *chrishughes24*.
* Day 27 - The first correct Lean solutions start to come in: *alexjbest* is the first for **Special Pythagorean Triple** and *chrishughes24* for **Fun modulo 5**
* Day 28 - *monadius* solved all 4 tasks in Coq and also submits a correct solution in Lean, being the first to submit solutions in two ITPs. 
* After roughly a month - *lasydler*, *jonathye* and *monadius* use a known Coq bug to **break the system**. They thus overtake *eberlm* with now 5 solved tasks. Using a soundness bug is considered okay in that task, only in the first four tasks it is disqualified. 


## Solutions for the Tasks:

### 1. Special Pythagorean Triple

Task was stated by Maximilian P. L. Haslbeck in Isabelle, and translated to Coq by Armaël Guéneau, to Lean by Kevin Kappelmann and to ACL2 by Sebastiaan Joosten.

The solution is the triple (375, 200, 425).


### 2. Fun modulo 5

Task was stated by Maximilian P. L. Haslbeck in Isabelle, and translated to Coq by Armaël Guéneau, to Lean by Kevin Kappelmann and to ACL2 by Sebastiaan Joosten.

For this task it is instructive to see that `m ^ 5 mod 10 = m` if `m < 10`.
To finish the proof one needs `((a mod b) ^ n) mod b = (a ^ n) mod b` which either is in your proof assistant's library or you need to prove it yourself. :)

### 3. XOR

Task was stated by Maximilian P. L. Haslbeck in Isabelle, and translated to Coq by Armaël Guéneau.

#### The default solution

For solving the task one has to notice that xor is commutative and associative. Similar to caching partial sums one thus can first calculate all partial XORs from index `0` to `i` and then get constant time access to `XOR i j f` by `xor (XOR 0 i f) (XOR 0 j f)`.

The program to solve the task in three phases:
1. Get the registers into a usable state: B should serve as accumulator in the next step and should be initialized to `False = XOR 0 0 f`.
2. The second phase collects the "partial XORs" into the *tmp* memory by `xor`ing one more element to the accumulator and storing the result at the right place. This takes a number of operations linear in `n`.
3. In the final phase, all queries are served in constant time each by using the lookup table in *tmp* and the observation above. This results again in a number of operations linear in `n`.


!!!!! TODO: LINK TO SOLUTION !!!!!


### 4. A funky grammar

Task was stated by Simon Wimmer in Isabelle, and translated to Coq by Armaël Guéneau.

#### The default solution


!!!!! TODO: explain solution !!!!!


!!!!! TODO: LINK TO SOLUTION !!!!!


#### An alternative solution (by Qinshi Wang)

> To prove M is included in L, I write a function that processes letters in a word w from set M from the end to the beginning. The function uses a stack to keep track of the letters already processed. The stack contains three kinds of elements S, A and B, that S stands for a word constructed by the rules of the context-free grammar, and A and B stand for letters a and b. The word resulted from concatenating all elements in the stack should be equal to the already processed suffix of w.  For each letter of w, the function first pushes A or B into the stack regarding the letter is a or b. Then the function checks the top elements in the stack. If it finds a prefix of the stack matches any of patterns AS*AS*B, AS*BS*A and BS*AS*A, then it replaces this prefix with an S.
> 
> If the result of the function is a single S in the stack, then it shows w is in L. So we only need to prove the result must be a single S for every word w that h(w)=0. First, if we define height H of a stack as the sum of heights of its elements that H(S)=0, H(A)=-1 and H(B)=2, then the height of the stack maintained by the function is always equal to the height of the already processed suffix. So the result must be a stack of height 0. Second, I characterize the shape of possible stacks after the function tries to replace some top elements with an S. Then I show if a stack is in this shapes and its height is 0, then it must be a single S. Thus, the theorem is solved.
> 
> I suggests this solution is simpler than the given approach. First, this proof is easier to understand. Second, this proof is totally constructive. It does not use excluded middle and it gives a clear way to construct a grammar tree of L. Third, although this proof uses more auxiliary definitions, it uses lemmas with more mechanical proofs. It is easier to automate these proofs.

https://competition.isabelle.systems/competitions/submission/2267/

!!!!! TODO: LINK TO SOLUTION !!!!!

### 5. Break the System

Task was stated by Simon Wimmer in Isabelle, Armaël Guéneau for Coq, Kevin Kappelmann in Lean and Sebastiaan Joosten in ACL2.

#### A simple Lean Solution

While the Lean judge was not yet tested thouroughly a simple trick was used by two contestants to break the system:
```
notation `false` := true
theorem soundness_bug : false := trivial
```

We fixed the problem by disallowing `notation` while still allowing `local notation`


#### A soundness bug for Coq

Three contestants use [a known soundness bug in Coq](https://github.com/coq/coq/issues/9294#issuecomment-450860504) to break the system.

We plan to use a PR for the Coq judge that closes the bug soon.








