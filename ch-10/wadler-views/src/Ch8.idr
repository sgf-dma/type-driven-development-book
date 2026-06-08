
module Ch8

import Data.Nat
import Data.SnocList
import Data.List.Views
import Decidable.Equality

import Ch5


%default total

public export
data Tree : Type -> Type where
  Leaf : (x : a) -> Tree a
  Branch : (left : Tree a) -> (right : Tree a) -> Tree a

-- All Injective proofs are not needed in fact.
Injective Leaf where
  injective Refl = Refl

Injective Branch where
  injective Refl = Refl

{l : Tree a} -> Injective (Branch l) where
  injective Refl = Refl

{r : Tree a} -> Injective (\l => Branch l r) where
  injective Refl = Refl

Uninhabited (Leaf x = Branch l r) where
  uninhabited Refl impossible

Uninhabited (Branch l r = Leaf x) where
  uninhabited Refl impossible

injectiveBranch : Branch xl xr = Branch yl yr -> (xl = yl, xr = yr)
injectiveBranch Refl = (Refl, Refl)

DecEq a => DecEq (Tree a) where
  decEq (Leaf x) (Leaf y) =
    case decEq x y of
         Yes prf => rewrite prf in Yes Refl
         -- I don't need 'Injective' in fact
         --No contra => No $ \eq => contra (injective eq)
         -- i may just pattern-match on Refl:
         No contra => No $ \Refl => contra Refl
  decEq (Branch xl xr) (Branch yl yr) =
    case decEq xl yl of
         Yes lprf => case decEq xr yr of
              Yes rprf => rewrite lprf in rewrite rprf in Yes Refl
              {-
              No contra => No $ rewrite lprf in \eqBranches =>
                            contra (injective eqBranches)
                            -}
              -- Here i also may do without Injective:
              No contra => No $ rewrite lprf in \Refl => contra Refl
         No contra => No $ \Refl => contra Refl
  decEq (Leaf _) (Branch yleft yright) = No uninhabited
  decEq (Branch xleft xright) (Leaf _) = No uninhabited

export
Eq a => Eq (Tree a) where
  Leaf x == Leaf y = x == y
  Branch xleft xright == Branch yleft yright = xleft == yleft && xright == yright
  _ == _ = False

-- This is left spine. Right spine is completely symmetrical.
public export
data SpineTree : Type -> Type where
  Spine : (x : a) -> (leafs : SnocList (SpineTree a)) -> SpineTree a

-- Total SpineTree length, including sub-trees.
spineLength : SpineTree a -> Nat
spineLength (Spine x Lin) = 1
-- Note, that i can't use `foldl` here because it'll won't pass totality
-- check. I should explicitly call function recursively with smaller argument.
spineLength (Spine x (leafs:<sp)) = spineLength sp + spineLength (Spine x leafs)

export
Eq a => Eq (SpineTree a) where
  Spine x Lin == Spine y Lin = x == y
  Spine x (xlefts:<xright) == Spine y (ylefts:<yright) =
    -- The same note here: i can't just use
    --      xlefts == ylefts
    -- i should explicitly call recursive function with smaller arguments to
    -- pass totality check.
    x == y && xright == yright && Spine x xlefts == Spine y ylefts
  _ == _ = False

-- FIXME: Use record.
public export
data SpineTree' : Type -> Type where
  Spine' : (x : a) -> (leafs : SnocList (SpineTree' a)) -> {depth : Nat} -> SpineTree' a

--spineDepth : SpineTree' a -> Nat
--spineDepth (Spine' _ {depth} _) = depth
--
--spineLeafs : SpineTree' a -> SnocList (SpineTree' a)
--spineLeafs (Spine' _ leafs) = leafs

--eqSpineTree : Eq a => (xs : SpineTree' a) -> (ys : SpineTree' a) ->
--                      {n : Nat} -> {auto prf : n = spineDepth xs} -> Bool
--eqSpineTree {n = Z} (Spine' x {depth = xd} xleafs) (Spine' y {depth = yd} yleafs) =
--eqSpineTree (Spine' x {depth = xd} xleafs) (Spine' y {depth = yd} yleafs) =
--  if xd != yd then False
--              else

export
treeToSpine : (tr : Tree a) -> SpineTree a
treeToSpine (Leaf x) = Spine x Lin
treeToSpine (Branch left right) =
  case treeToSpine left of
       Spine x leafs => Spine x (leafs :< treeToSpine right)

export
spineToTree : (str : SpineTree a) -> Tree a
spineToTree (Spine x Lin) = Leaf x
spineToTree (Spine x (lefts:<right)) =
  Branch (spineToTree (Spine x lefts)) (spineToTree right)

public export
data SpineTree2 : Type -> Type where
  Spine2 : (x : a) -> (leafs : MySnocList (SpineTree2 a)) -> SpineTree2 a

export
treeToSpine2 : (tr : Tree a) -> SpineTree2 a
treeToSpine2 (Leaf x) = Spine2 x MyNilSnoc
treeToSpine2 (Branch left right) =
  case treeToSpine2 left of
       Spine2 x leafs => Spine2 x (MySnoc (mySnocOut leafs) (treeToSpine2 right))

public export
data SpineTree3 : Type -> Type where
  Spine3 : (x : a) -> (leafs : MySnocListRec (SpineTree3 a)) -> SpineTree3 a

export
treeToSpine3 : (tr : Tree a) -> SpineTree3 a
treeToSpine3 (Leaf x) = Spine3 x MyNilSnocRec
treeToSpine3 (Branch left right) =
  case treeToSpine3 left of
       Spine3 x leafs => Spine3 x (MySnocRec leafs (treeToSpine3 right))

-- Recursive spine:
-- In fact, i already have it: last element from 'leafs' list is the spine for
-- the right subtree (i.e. right recursive spine), and the rest of the 'leafs'
-- list (all, except last element) is the spine for the left subtree.
-- But without 'Tree a' in type all this has no sense, because it'll be just
-- _some_ spine values and they can contain literally everything.
-- Therefore, to actually make recursive arguments useful, i need to define
-- 'SpineTree' as a type dependent on 'Tree'. But there's a problem with
-- 'List', which can't contain values of different type.

-- So, i may just replace recursive 'List' constructor with recursive 'Spine'
-- constructor and get rid of list altogether.
public export
data SpineTree4 : (Tree a) -> Type where
  -- I have no empty list now, so i need a special constructor corresponding to 'Lin'.
  SpineLeaf4 : (x : a) -> SpineTree4 (Leaf x)
  Spine4 : (x : a) ->
                -- I may use multiplicity 0 too, but then some implementation
                -- won't be possible (see below).
                --{0 tleft, tright : Tree a} ->
                {tleft, tright : Tree a} ->
                (recLeft : SpineTree4 tleft) -> (recRight : SpineTree4 tright) ->
                SpineTree4 (Branch tleft tright)

export
Eq (SpineTree4 tr) where
  _ == _ = True

-- In fact, this does not differ from 'treeToSpine' at all: the same
-- recursion, the same case to extract 'x'. I may replace ':<' constructors in
-- 'treeToSpine' with 'Spine4' applications here and i'll get roughly the
-- same structure. The only difference is that 'Spine4' repeats leftmost
-- 'x' at each level in left branches.
export
treeToSpine4 : (tr : Tree a) -> SpineTree4 tr
treeToSpine4 (Leaf x) = SpineLeaf4 x
treeToSpine4 (Branch left right) =
  case treeToSpine4 left of
       sp@(SpineLeaf4 x) => Spine4 x sp (treeToSpine4 right)
       sp@(Spine4 x _ _) => Spine4 x sp (treeToSpine4 right)

-- Requires multiplicity of 'tleft' and 'tright' to be non-zero.
export
spineToTree4' : {tr : Tree a} -> SpineTree4 tr -> Tree a
spineToTree4' _ = tr

export
spineToTree4 : {0 tr : Tree a} -> SpineTree4 tr -> Tree a
spineToTree4 (SpineLeaf4 x) = Leaf x
spineToTree4 (Spine4 x recLeft recRight) =
  Branch (spineToTree4 recLeft) (spineToTree4 recRight)

export
spineTree4_1 : {tr : Tree a} -> SpineTree4 tr -> SpineTree a
spineTree4_1 (SpineLeaf4 x) = Spine x Lin
spineTree4_1 (Spine4 x recLeft recRight) =
  case spineTree4_1 recLeft of
       Spine _ lefts => Spine x (lefts :< spineTree4_1 recRight)

export
spineTree1_4 : SpineTree a -> (tr : Tree a ** SpineTree4 tr)
spineTree1_4 (Spine x Lin) = (Leaf x ** SpineLeaf4 x)
spineTree1_4 (Spine x (lefts:<right)) =
  case spineTree1_4 (Spine x lefts) of
       (tleft ** recLeft) => case spineTree1_4 right of
            (tright ** recRight) => (Branch tleft tright ** Spine4 x recLeft recRight)

tree1 : Tree String
tree1 = Branch (Branch (Leaf "f") (Leaf "a")) (Leaf "b")

tree2 : Tree String
tree2 = Branch (Leaf "f") (Leaf "a")

tree3 : Tree String
tree3 = Branch (Leaf "f") (Branch (Leaf "a") (Leaf "b"))

tree4 : Tree String
tree4 = Branch (Branch (Branch (Leaf "f") (Leaf "a")) (Branch (Leaf "c") (Leaf "d"))) (Leaf "b")
