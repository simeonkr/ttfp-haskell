import Data.Either

import TTFP


-- A ⇒ A
ex1 = do
    dt0 <- assume (Var "x") (Generic "A")
    dt1 <- implIntro (Var "x") dt0
    return dt1

-- (A ⇒ B) and (B ⇒ C) imply (A ⇒ C)
ex2 = do
    dt0 <- assume (Var "a") (Impl (Generic "A") (Generic "B"))
    dt1 <- assume (Var "x") (Generic "A")
    dt2 <- assume (Var "b") (Impl (Generic "B") (Generic "C"))
    dt3 <- implElim dt0 dt1
    dt4 <- implElim dt2 dt3
    dt5 <- implIntro (Var "x") dt4
    return dt5

-- ((A v B) ⇒ C) ⇒ ((A ⇒ C) ∧ (B ⇒ C))
ex3 = do
    dt0 <- assume (Var "x") (Generic "A")
    dt1 <- assume (Var "y") (Impl (Or (Generic "A") (Generic "B")) (Generic "C"))
    dt2 <- orIntroLeft (Generic "B") dt0
    dt3 <- implElim dt1 dt2
    dt4 <- implIntro (Var "x") dt3

    dt5 <- assume (Var "x") (Generic "B")
    dt6 <- orIntroRight (Generic "A") dt5
    dt7 <- implElim dt1 dt6
    dt8 <- implIntro (Var "x") dt7

    dt9 <- andIntro dt4 dt8
    dt10 <- implIntro (Var "y") dt9
    return dt10

-- ((A ⇒ C) ∧ (B ⇒ C)) ⇒ ((A v B) ⇒ C)
ex4 = do
    dt0 <- assume (Var "p") (And (Impl (Generic "A") (Generic "C"))
                                 (Impl (Generic "B") (Generic "C")))
    dt1 <- assume (Var "z") (Or (Generic "A") (Generic "B"))
    dt2 <- andElimFst dt0
    dt3 <- andElimSnd dt0
    dt4 <- orElim dt1 dt2 dt3
    dt5 <- implIntro (Var "z") dt4
    dt6 <- implIntro (Var "p") dt5
    return dt6

-- (∀x:A).(B ⇒ C) ⇒ (∀x:A).B ⇒ (∀x:A).C
ex5 = do
    dt0 <- assume (Var "x") (Generic "A")
    dt1 <- assume (Var "r") (Forall (Var "x") (Generic "A") (Impl (Generic "B") (Generic "C")))
    dt2 <- forallElim dt0 dt1
    dt3 <- assume (Var "p") (Forall (Var "x") (Generic "A") (Generic "B"))
    dt4 <- forallElim dt0 dt3
    dt5 <- implElim dt2 dt4
    dt6 <- forallIntro (Var "x") dt5
    dt7 <- implIntro (Var "p") dt6
    dt8 <- implIntro (Var "r") dt7
    return dt8

-- ((∃x:X).P) ⇒ Q implies (∀x:X).(P ⇒ Q)
ex6 = do
    dt0 <- assume (Var "x") (Generic "X")
    dt1 <- assume (Var "p") (Generic "P")
    dt2 <- existsIntro (Var "x") dt0 dt1
    dt3 <- assume (Var "e") (Impl (Exists (Var "x") (Generic "X") (Generic "P")) (Generic "Q"))
    dt4 <- implElim dt3 dt2
    dt5 <- implIntro (Var "p") dt4
    dt6 <- forallIntro (Var "x") dt5
    return dt6

-- (∀x:X).(P ⇒ Q) implies ((∃x:X).P) ⇒ Q  (when x not free in Q)
ex7 = do
    dt0 <- assume (Var "p") (Exists (Var "x") (Generic "X") (Generic "P"))
    dt1 <- existsElim2 dt0
    dt2 <- existsElim1 dt0
    dt3 <- assume (Var "e") (Forall (Var "x") (Generic "X") (Impl (Generic "P") (Generic "Q")))
    dt4 <- forallElim dt2 dt3
    dt5 <- implElim dt4 dt1
    dt6 <- implIntro (Var "p") dt5
    return dt6

-- Predecessor function: (∀x:N).((x ≠ 0) ⇒ N)
ex8 = do
    dt0 <- assume (Var "r") (I NatType Zero Zero)
    dt1 <- assume (Var "z") (Impl (I NatType Zero Zero) Empty)
    dt2 <- implElim dt1 dt0
    dt3 <- emptyElim NatType dt2
    dt4 <- implIntro (Var "z") dt3

    dt5 <- assume (Var "n") NatType
    dt6 <- assume (Var "c") (Impl (Impl (I NatType (Var "n") Zero) Empty) NatType)
    dt7 <- assume (Var "p") (Impl (I NatType (Succ (Var "n")) Zero) Empty)
    dt8 <- natIntroSucc dt5

    -- The next two rules ensure that 'p' appears in the derivation chain leading to the last statement
    dt8i <- andIntro dt7 dt8
    dt8e <- andElimSnd dt8i
    dt9 <- implIntro (Var "p") dt8e

    -- Same situation here (TODO: maybe have a special ⇒ rule to avoid this)
    dt9i <- andIntro dt6 dt9
    dt9e <- andElimSnd dt9i
    dt10 <- implIntro (Var "c") dt9e

    dt11 <- forallIntro (Var "n") dt10

    dt12 <- natElim dt4 dt11

    return dt12


