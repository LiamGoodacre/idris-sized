module Sized

%default total

namespace Sized
  ||| Types with a size and a means to look up values given a finite
  ||| index less than the size
  class Sized (t : Type) where
    ||| Determine the size of a `t`
    size : t -> Nat
    ||| Look up the type in `xs` at a given finite index
    typeAt : (xs : t) -> Fin (size xs) -> Type
    ||| Look up a value in `xs` at a given finite index
    termAt : (xs : t) -> (f : Fin (size xs)) -> typeAt xs f

  ||| Sized types that can be updated at a particular index
  class Sized t => Updated (t : Type) where
    ||| Determine the type expected at a given finite index
    typeFor : (xs : t) -> Fin (size xs) -> Type
    ||| Determine the result type of inserting a value at a given finite index
    resultFor : (xs : t) -> (f : Fin (size xs)) -> typeFor xs f -> Type
    ||| Insert a value at a given finite index into a term `xs`
    updateAt : (xs : t) -> (f : Fin (size xs)) -> (i : typeFor xs f) -> resultFor xs f i


namespace Fin
  ||| Proof that a finite nat `f : Fin n` is less than its bound `n`
  finLtNat : (f : Fin n) -> lt (finToNat f) n = True
  finLtNat FZ = Refl
  finLtNat (FS x) = finLtNat x


namespace List
  instance Sized (List a) where
    size = List.length
    typeAt _ _ = a
    termAt (x :: _) FZ = x
    termAt (_ :: xs) (FS y) = List.index (finToNat y) xs (finLtNat y)

  instance Updated (List a) where
    typeFor _ _ = a
    resultFor _ _ _ = List a
    updateAt (_ :: xs) FZ v = v :: xs
    updateAt (x :: xs) (FS f) v = ?updateAt_List


namespace Vect
  instance Sized (Vect n a) where
    size {n} _ = n
    typeAt _ _ = a
    termAt xs f = Vect.index f xs

  instance Updated (Vect n a) where
    typeFor _ _ = a
    resultFor {n} _ _ _ = Vect n a
    updateAt xs f v = Vect.replaceAt f v xs


namespace HVect
  data HVect : Vect n Type -> Type where
    Nil  : HVect []
    (::) : t -> HVect ts -> HVect (t :: ts)

  head : HVect (h :: _) -> h
  head (x :: _) = x

  tail : HVect (_ :: hs) -> HVect hs
  tail (_ :: xs) = xs

  index : {hs : Vect n Type} -> (f : Fin n) -> HVect hs -> Vect.index f hs
  index FZ (x :: xs) = x
  index (FS f) (x :: xs) = index f xs

  instance Sized (HVect hs) where
    size {hs} _ = size hs
    typeAt {hs} _ f = Vect.index f hs
    termAt xs f = index f xs

  instance Updated (HVect hs) where
    -- like: typeFor _ _ = forall a. a
    typeFor _ _ = ?typeFor_HVect
    -- like: resultFor xs f v = Vect.replaceAt f (typeFor xs f) hs
    resultFor xs f v = ?resultFor_HVect
    -- not yet considered
    updateAt xs f v = ?updateAt_HVect


namespace Demo
  xs : HVect [Int, Bool]
  xs = [42, True]

  v0 : typeAt xs 0
  v0 = termAt xs 0

  v1 : typeAt xs 1
  v1 = termAt xs 1
