module Turing

%default total

-- Re-implementation of 'Totality vs Turing Completeness' by Conor McBride
--

data General : (S: Type) -> (T: S -> Type) -> (X : Type) -> Type where
  Res   : x -> General s t x
  Req   : {S : Type} -> (s: S) -> (t s -> General S t x) -> General S t x

fold : {S : Type} -> (x -> y) -> ((s:S) -> (t s -> y) -> y) -> General S t x -> y
fold r c (Res x)     = r x
fold r c (s `Req` k) = c s (\t => fold r c (k t))

call : {S: Type} -> (s:S) -> General S t (t s)
call s = s `Req` Res

PiG : (S : Type) -> (T: S -> Type) -> Type
PiG S T = (s : S) -> General S T (T s)

halting : (s -> Bool) -> (s -> s) -> PiG s (const s)
halting stop step start with (stop start)
                         | True  = Res start
                         | False = call (step start)


-- namespace Kleisli
--   data Kleisli : -- {x: Type} -> {y: Type} ->  
--                  {F: Type -> Type} -> {G: Type -> Type} -> 
--                  (M : F i -> G j) -> Type where
