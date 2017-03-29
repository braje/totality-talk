module Turing

%default total

-- Re-implementation of 'Totality vs Turing Completeness' by Conor McBride
--

-- data General : (S' : Type) -> (T : S' -> Type) -> (X : Type) -> Type where
--   Res : {S' : Type} -> {T : S' -> Type} -> {X : Type} ->
--         (x:X) -> General S' T X
--   Req : {S' : Type} -> {T : S' -> Type} -> {X : Type} ->
--         (s : S') -> (T s -> General S' T X) -> General S' T X

data General : (s : Type) -> (t : s -> Type) -> (x : Type) -> Type where
  Res   : x -> General s t x
  Req   : (s' : s) -> (t s' -> General s t x) -> General s t x

-- fold : {S' : Type} -> {T : S' -> Type} -> {X : Type} -> {Y : Type} ->
--        (X -> Y) -> ((s:S') -> (T s -> Y) -> Y) -> General S' T X -> Y
-- fold r c (Res x)     = r x
-- fold r c (s `Req` k) = c s (\t => fold r c (k t))

fold : {S' : Type} -> (x -> y) -> ((s:S') -> (t s -> y) -> y) -> General S' t x -> y
fold r c (Res x)     = r x
fold r c (s `Req` k) = c s (\t => fold r c (k t))

call : (s':s) -> General s t (t s')
call s = s `Req` Res

  -- call : {S' : Type} -> {T : S' -> Type} -> (s:S') -> General S' T (T s)
  -- call s = s `Req` Res


PiG : (S' : Type) -> (T : S' -> Type) -> Type
PiG S' T = (s : S') -> General S' T (T s)

PiG' : (s:Type) -> (s -> Type) -> Type
PiG' SS T = (s:SS) -> General SS T (T s)

PiG'' : (s:Type) -> (s -> Type) -> Type
PiG'' s t = (s':s) -> General s t (t s')


halting : (s -> Bool) -> (s -> s) -> PiG s (const s)
halting stop step start with (stop start)
                         | True  = Res start
                         | False = call (step start)
