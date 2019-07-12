module TTFP where

import Data.Either
import Data.List
import Data.Maybe


-- Syntax

{- TODO: make Type a class instead of a data type
   for better typechecking and extensibility -}
data Type = Generic String |
            And Type Type |
            Or Type Type |
            Impl Type Type |
            Empty |
            Forall Obj Type Type |
            Exists Obj Type Type |
            TypeSubst Type Obj Obj |
            BoolType |
            NatType |
            TreeType |
            EqType
            deriving Eq
            
neg a = Impl a Empty
equiv a b = (And (Impl a b) (Impl b a))

data Obj = Var String |
           Pr Obj Obj |
           Fst Obj |
           Snd Obj |
           Inl Obj |
           Inr Obj |
           Lambda Obj Obj |
           Appl Obj Obj |
           Cases Obj Obj Obj |
           Abort Obj |
           Subst Obj Obj Obj |
           T |
           F |
           If Obj Obj Obj |
           Zero |
           Succ Obj
           deriving Eq

data St = St Obj Type | Discharged St deriving Eq

data DT = DT St [DT] deriving Eq

data InfErr = InfErr String


-- Printing

instance Show Type where
    show (Generic a) = a
    show (And a b) = binaryOpShow "∧" a b
    show (Or a b) = binaryOpShow "v" a b
    show (Impl a b) = binaryOpShow "⇒" a b
    show Empty = "⊥"
    show (Forall x a pt) = quantifShow "∀" x a pt
    show (Exists x a pt) = quantifShow "∃" x a pt
    show (TypeSubst t x to) = substShow t x to
    
unaryOpShow op x = "(" ++ op ++ show x ++ ")"
binaryOpShow op x y = "(" ++ show x ++ " " ++ op ++ " " ++ show y ++ ")"
quantifShow op x a pt = "(" ++ op ++ show x ++ ":" ++ show a ++ ")." ++ show pt
substShow t x to = show t ++ "[" ++ show to ++ "/" ++ show x ++ "]"

instance Show Obj where
    show (Var x) = x
    show (Pr p q) = "(" ++ show p ++ ", " ++ show q ++ ")"
    show (Fst r) = "fst " ++ show r
    show (Snd r) = "snd " ++ show r
    show (Inl r) = "inl " ++ show r
    show (Inr r) = "inr " ++ show r
    show (Lambda x e) = "λ" ++ show x ++ "." ++ show e
    show (Appl q a) = "(" ++ show q ++ " " ++ show a ++ ")"
    show (Cases p f g) = "cases " ++ show p ++ " " ++ show f ++ " " ++ show g
    show (Subst p x to) = substShow p x to
    
instance Show St where
    show (St x a) = show x ++ " : " ++ show a
    show (Discharged s) = "[" ++ show s ++ "]"
    
instance Show DT where
    show dt = "\n" ++ show_ 0 dt where        
        show_ indent (DT s dts) = concat (replicate indent "  ") ++ show s ++
            if null dts then " *" else "\n" ++ intercalate "\n" (map (show_ (indent+1)) dts)
    
instance Show InfErr where
    show (InfErr s) = "Inference error: " ++ s


-- Helper functions

subst :: Obj -> Obj -> Obj -> Obj
subst e x to = if x == to then e else if e == x then to else case e of
    (Var p) -> (Subst (Var p) x to)
    (Pr e1 e2) -> Pr (subst e1 x to) (subst e2 x to)
    (Fst e) -> Fst (subst e x to)
    (Snd e) -> Snd (subst e x to)
    (Inl e) -> Inl (subst e x to)
    (Inr e) -> Inr (subst e x to)
    (Lambda e1 e2) -> Lambda (subst e1 x to) (subst e2 x to)
    (Appl e1 e2) -> Appl (subst e1 x to) (subst e2 x to)
    (Cases e1 e2 e3) -> Cases (subst e1 x to) (subst e2 x to) (subst e3 x to)
        
typeSubst :: Type -> Obj -> Obj -> Type
typeSubst e x to = if x == to then e else case e of
    (Generic a) -> (TypeSubst (Generic a) x to)
    (And a b) -> And (typeSubst a x to) (typeSubst b x to)
    (Or a b) -> Or (typeSubst a x to) (typeSubst b x to)
    (Impl a b) -> Impl (typeSubst a x to) (typeSubst b x to)
    Empty -> Empty
    (Forall xe xt pt) -> if xe == x then (Forall to xt pt) else e
    (Exists xe xt pt) -> if xe == x then (Forall to xt pt) else e

roots :: DT -> [St]
roots (DT s []) = [s]
roots (DT s xs) = concat $ map roots xs

lookupObj :: Obj -> DT -> Maybe Type
lookupObj x0 (DT s@(St x t) dt) = if x == x0 then Just t 
                                  else let allFound = mapMaybe (lookupObj x0) dt in
                                      if null allFound then Nothing else Just $ head allFound
lookupObj x0 (DT (Discharged (St x t)) dt) = lookupObj x0 (DT (St x t) dt)

discharge :: Obj -> DT -> DT
discharge x0 (DT s@(St x t) dt) = DT (if x == x0 then Discharged s else s) 
                                     (map (discharge x0) dt)
discharge x0 (DT s@(Discharged (St x t)) dt) = DT s (map (discharge x0) dt)
                                     
makeDTErrMsg msg dts = InfErr $ msg ++ "\nDerivation trees are:\n" 
                              ++ intercalate "\n" (map show dts) ++ "\n"                              
makeObjErrMsg msg obj = InfErr $ msg ++ " (" ++ show obj ++ ")"


-- Assumption

assume :: Obj -> Type -> Either InfErr DT
assume x@(Var _) a = Right $ DT (St x a) []
assume x _ = Left $ makeObjErrMsg "Incorrect assumption" [x]


-- And

andIntro :: DT -> DT -> Either InfErr DT
andIntro dt1@(DT (St p a) _) dt2@(DT (St q b) _) = Right $ DT (St (Pr p q) (And a b)) [dt1, dt2]
andIntro dt1 dt2 = Left $ makeDTErrMsg "Cannot apply ∧ introduction" [dt1, dt2]

andElimFst :: DT -> Either InfErr DT
andElimFst dt@(DT s@(St r (And a b)) _) = Right $ (DT (St (Fst r) a) [dt])
andElimFst dt = Left $ makeDTErrMsg "Cannot apply ∧ elimination" [dt]

andElimSnd :: DT -> Either InfErr DT
andElimSnd dt@(DT s@(St r (And a b)) _) = Right $ (DT (St (Snd r) b) [dt])
andElimSnd dt = Left $ makeDTErrMsg "Cannot apply ∧ elimination" [dt]

andComp :: Obj -> Either InfErr Obj
andComp (Fst (Pr p q)) = Right p
andComp (Snd (Pr p q)) = Right q
andComp x = Left $ makeObjErrMsg "Cannot apply ∧ computation" [x]


-- Impl

implIntro :: Obj -> DT -> Either InfErr DT
implIntro x dt@(DT (St e b) _) = let am = lookupObj x dt in
    case am of
        Nothing -> Left $ makeObjErrMsg "Cannot apply ⇒ introduction. Object not found." [x]
        Just a -> Right $ DT (St (Lambda x e) (Impl a b)) [discharge x dt]
implIntro _ dt = Left $ makeDTErrMsg "Cannot apply ⇒ introduction" [dt]

implElim :: DT -> DT -> Either InfErr DT
implElim dt1@(DT s1@(St q (Impl a b)) _) dt2@(DT s2@(St r aa) _)
    | (a /= aa) = Left $ makeDTErrMsg "Cannot apply ⇒ elimination. Type mismatch." [dt1, dt2]
    | otherwise = return $ DT (St (Appl q r) b) [dt1, dt2]
implElim dt1 dt2 = Left $ makeDTErrMsg "Cannot apply ⇒ elimination" [dt1, dt2]

implComp :: Obj -> Either InfErr Obj
implComp (Appl (Lambda x@(Var _) e) r) = Right $ subst e x r
implComp x = Left $ makeObjErrMsg "Cannot apply ⇒ computation" [x]


-- Or

orIntroLeft :: Type -> DT -> Either InfErr DT
orIntroLeft b dt@(DT (St q a) _) = Right $ DT (St (Inl q) (Or a b)) [dt]
orIntroLeft _ dt = Left $ makeDTErrMsg "Cannot apply v introduction" [dt]

orIntroRight :: Type -> DT -> Either InfErr DT
orIntroRight a dt@(DT (St r b) _) = Right $ DT (St (Inr r) (Or a b)) [dt]
orIntroRight _ dt = Left $ makeDTErrMsg "Cannot apply v introduction" [dt]

orElim :: DT -> DT -> DT -> Either InfErr DT
orElim dt1@(DT (St p (Or a b)) _) dt2@(DT (St f (Impl aa c)) _) dt3@(DT (St g (Impl bb cc)) _)
    | (a /= aa) || (b /= bb) || (c /= cc) = Left $ makeDTErrMsg "Cannot apply v elimination" [dt1, dt2, dt3]
    | otherwise = Right $ DT (St (Cases p f g) c) [dt1, dt2, dt3]
orElim dt1 dt2 dt3 = Left $ makeDTErrMsg "Cannot apply v elimination" [dt1, dt2, dt3]

orComp :: Obj -> Either InfErr Obj
orComp (Cases (Inl q) f g) = Right (Appl f q)
orComp (Cases (Inr r) f g) = Right (Appl g r)
orComp x = Left $ makeObjErrMsg "Cannot apply v computation" [x]


-- Empty

emptyElim :: Type -> DT -> Either InfErr DT
emptyElim a dt@(DT (St p Empty) _) = Right $ DT (St (Abort p) a) [dt]
emptyElim _ dt = Left $ makeDTErrMsg "Cannot apply ⊥ elimination" [dt]


-- Forall

forallIntro :: Obj -> DT -> Either InfErr DT
forallIntro x dt@(DT (St p pt) _) = let am = lookupObj x dt in
    case am of
        Nothing -> Left $ makeObjErrMsg "Cannot apply ∀ introduction. Object not found." [x]
        Just a -> Right $ DT (St (Lambda x p) (Forall x a pt)) [discharge x dt]
forallIntro _ dt = Left $ makeDTErrMsg "Cannot apply ∀ introduction" [dt]

forallElim :: DT -> DT -> Either InfErr DT
forallElim dt1@(DT (St a at) _) dt2@(DT (St f (Forall x aat pt)) _) = 
    Right $ DT (St (Appl f a) (typeSubst pt x a)) [dt1, dt2]
    
forallComp :: Obj -> Either InfErr Obj
forallComp (Appl (Lambda x p) a) = Right $ subst p x a
forallComp x = Left $ makeObjErrMsg "Cannot apply ∀ computation" [x]


-- Exists

existsIntro :: Obj -> DT -> DT -> Either InfErr DT
existsIntro x dt1@(DT (St a at) _) dt2@(DT (St p pt) _) = 
    Right $ DT (St (Pr a p) (Exists x at (typeSubst pt a x))) [dt1, dt2]
existsIntro _ dt1 dt2 = Left $ makeDTErrMsg "Cannot apply ∃ introduction" [dt1, dt2] 
    
existsElim1 :: DT -> Either InfErr DT
existsElim1 dt@(DT (St p (Exists x a pt)) _) = Right $ DT (St (Fst p) a) [dt]
existsElim1 dt = Left $ makeDTErrMsg "Cannot apply ∃ elimination (1)" [dt]

existsElim2 :: DT -> Either InfErr DT
existsElim2 dt@(DT (St p (Exists x a pt)) _) = 
    Right $ DT (St (Snd p) (typeSubst pt x (Fst p))) [dt]
existsElim2 dt = Left $ makeDTErrMsg "Cannot apply ∃ elimination (2)" [dt]

existsComp :: Obj -> Either InfErr Obj
existsComp (Fst (Pr p q)) = Right p
existsComp (Snd (Pr p q)) = Right q
existsComp x = Left $ makeObjErrMsg "Cannot apply ∃ computation" [x]


-- BoolType

boolIntroTrue :: DT -> Either InfErr DT
boolIntroTrue dt = Right $ DT (St T BoolType) [dt]

boolIntroFalse :: DT -> Either InfErr DT
boolIntroFalse dt = Right $ DT (St F BoolType) [dt]

boolElim :: DT -> DT -> DT -> Either InfErr DT
boolElim dt1@(DT (St tr BoolType) _) dt2@(DT (St c ct) _) dt3@(DT (St d cct) _)
    | ct /= cct = Left $ makeDTErrMsg "Cannot apply bool elimination. Type mismatch." [dt1, dt2, dt3]
    | otherwise = Right $ DT (St (If tr c d) ct) [dt1, dt2, dt3]
    
boolComp :: Obj -> Either InfErr Obj
boolComp (If T c d) = Right c
boolComp (If F c d) = Right d
boolComp x = Left $ makeObjErrMsg "Cannot apply bool computation" [x]

