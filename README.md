# Minamoto Kanren

Minimal relational programming utilities.

Basically a re-implementation of Sokuza Kanren in Haskell and Go.

## Difference between Minamoto Kanren and Sokuza Kanren

The difference is that it's in Haskell and Golang instead of Scheme. Other than the obvious difference of us having to explicitly specify the type of terms that are available within the language:

+ For the Haskell version: Since Haskell is lazy, the eta-expansion required in Scheme is not needed. See below.
+ For the Golang version: I deliberately restrained myself from using anonymous functions and defunctionalize by hand; the result is something that some might call the "Command Pattern" or the "Interpreter Pattern" and can be re-done in languages like C with much less extra effort.

## Difference between `Main.hs` and `MainWrong.hs`

`MainWrong.hs` is technically also my first attempt.

The main difference between `MainWrong.hs` and `Main.hs`, obviously, is that the former is a wrong implementation and the latter is the right one; but we must understand what is exactly wrong here.

In the definition of `appendo`, the original calls for 3 fresh logic variables - fresh, as in not used in any way in the subst. In `MainWrong.hs` I attempt to solve this by adding the `newvar` function, which is incorrectly implemented since it checks the left-hand side of each bind but not the right-hand side. Technically one can still make it work by implementing the right-hand side, but generating new variable names this way is too bothersome (and inefficient when the subst grows big).

One way to make sure we have properly fresh variables is to weave in a gensym, as seen in `Main.hs`:

``` haskell
-- the second field is the gensym base.
type State = (Subst, Integer)
type Goal = State -> [State]

-- generate a new variable and returns the state with the used gensym.
fresh :: State -> (Term, State)
fresh (s, k) = (Var ("V_" ++ show k), (s, k + 1))
```

A side effect of doing things this way is that we need to explicitly specify which state we're going to put our goal through, as shown in the definition of `appendo` in `Main.hs`:

``` haskell
    -- ...
    (\s ->
       -- NOTE: we cannot do `let (h, s) = fresh s` here because haskell.
       let (h, s1) = fresh s
       in let (t, s2) = fresh s1
          in let (l3p, s3) = fresh s2
             in (
         conjN [
             conso h t l1  -- [H|T] = L1
             , conso h l3p l3  -- [H|L3P] = L3
             , appendo t l2 l3p -- append(T, L2, L3P)
             ]
         ) s3
```

In Sokuza Kanren, this problem is non-existent for the following facts:

+ Variables are represented as vectors, which, when created by calling `var`, creates a new object with a new address.
+ Sokuza Kanren's subst lookup used `assq` instead of `assoc`. The former chcks only addresses but the latter checks equality by actual value, which would've caused the same problem.

In muKanren, this problem is non-existent for the reason that `call/fresh` is technically higher-order abstract syntax.

