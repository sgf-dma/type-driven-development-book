
module Schema

import Data.String
import Data.Vect
import Control.Arrow
import Data.Morphisms
import Control.Category

import Utils

export infixr 5 .+.

public export
data Schema = SString
            | SInt
            | SChar
            | (.+.) Schema Schema

export
displaySchema : (parens : Bool) -> Schema -> String
displaySchema _ SInt = "Int"
displaySchema _ SString = "String"
displaySchema _ SChar = "Char"
displaySchema parens ((.+.) s1 s2) =
  -- Show parens around both sides of .+. . It's easy to read.
  showParens parens (displaySchema True s1 ++ " " ++ displaySchema True s2)
  where
    showParens : Bool -> String -> String
    showParens True input = "(" ++ input ++ ")"
    showParens False input = input

export
parseSchemaPrefix : String -> Maybe (Schema, String)
parseSchemaPrefix input =
  let m1 = parseToken input
  in  (m1 >>= applyKleisli {f = Maybe} (
                second (Kleisli parseSchemaPrefix)
                >>> arrow (\(s1, (s2, rest)) => (s1 .+. s2, rest))
              )
      ) <|> m1
  where
    parseToken : String -> Maybe (Schema, String)
    parseToken input =
      -- I accept tokens with leading spaces, so `ltrim` first.
      case span (\c => c /= ' ' && c /= '(' && c /= ')') (ltrim input) of
           ("String", rest) => pure (SString, rest)
           ("Int", rest) => pure (SInt, rest)
           ("Char", rest) => pure (SChar, rest)
           ("", rest) => case strM rest of
                -- I may handle spaces explicitly or i may just skip them as
                -- "leading spaces" with `ltrim`, as i did above.
                --StrCons ' ' rest' => parseSchemaPrefix rest' -- Right associativity.
                StrCons '(' rest' => closeParen parseSchemaPrefix rest'
                StrCons ')' _ => Nothing
                _ => Nothing
           _ => Nothing

public export
TypeSchema : Type -> Maybe Schema
TypeSchema String = Just SString
TypeSchema Int = Just SInt
TypeSchema Char = Just SChar
TypeSchema (a, b) = (.+.) <$> TypeSchema a <*> TypeSchema b
TypeSchema _ = Nothing

public export
SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (a .+. b) = (SchemaType a, SchemaType b)

export
display : {scm : Schema} -> SchemaType scm -> String
display {scm = SString} x = show x
display {scm = SInt} x = show x
display {scm = SChar} x = show x
display {scm = (.+.) a b} (x, y) = "(" ++ display x ++ ", " ++ display y ++ ")"

-- Parse value according to Schema. Parts of Schema, which require braces,
-- require them in a value too. Comma (for tuples) is not used in value, just
-- space.
export
parsePrefix : (parens : Bool)
            -> (scm : Schema)
            -> (input : String)
            -> Maybe (SchemaType scm, String)
parsePrefix _ SInt input =
    parseInt input <|> parseParens (parsePrefix False SInt) input
  where
    parseInt : (inp : String) -> Maybe (Int, String)
    parseInt inp = case span isDigit (ltrim inp) of
                        ("", _) => Nothing
                        (s, rest) => Just (cast s, rest)
parsePrefix _ SString input =
    (getQuoted . unpack . ltrim $ input)
    <|> parseParens (parsePrefix False SString) input
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"' :: rs) =
       case span (/= '"') rs of
            (quoted, '"' :: rest) => Just (pack quoted, pack rest)
            _ => Nothing
    getQuoted _ = Nothing
parsePrefix _ SChar input =
    getQuoted input <|> parseParens (parsePrefix False SChar) input
  where
    getQuoted : String -> Maybe (Char, String)
    getQuoted input =
      case strUncons1 3 (ltrim input) of
           Just (['\'', c, '\''], rest) => Just (c, rest)
           _ => Nothing
parsePrefix parens ((.+.) a b) input =
  let m = \inp => flip applyKleisli inp $
                  parse True a
                  >>> second (parse False b)
                  >>> arrow (\(left, (right, rest)) => ((left, right), rest))
  in  parseParens (parsePrefix False (a .+. b)) input
      <|> if parens then Nothing else m input
  where
    parse : (parens2 : Bool) -> (scm : Schema) -> Kleislimorphism Maybe String (SchemaType scm, String)
    parse parens2 = Kleisli .* (parsePrefix parens2)

-- parsePrefix' requires one or more spaces between elements.
parsePrefix' : (scm : Schema) -> String -> Maybe (SchemaType scm, String)
parsePrefix' SInt input =
  case span isDigit input of
       ("", _) => Nothing
       (s, rest) => Just (cast s, rest)
parsePrefix' SString input =
  case strM input of
       StrCons '"' rs => let (val, rs') = span (/= '"') rs
                         in  case strM rs' of
                                  StrCons _ rest => Just (val, rest)
                                  _  => Nothing
       _ => Nothing
parsePrefix' SChar input = ?notImplemented
parsePrefix' ((.+.) a b) input = do
  (left, rr) <- parsePrefix' a input
  case span (== ' ') rr of
       (_, "") => Nothing
       ("", _) => Nothing
       (l, rr') => do
          (right, rest) <- parsePrefix' b (ltrim rr')
          pure ((left, right), rest)

export
schemaHeight : Schema -> Nat
schemaHeight (s1 .+. s2) = S (maximum (schemaHeight s1) (schemaHeight s2))
schemaHeight _ = 0

-- List all Schema subtrees.

-- List of all Schema subtrees with their height.
export
allSubtrees : Schema -> List (Nat, Schema) -> List (Nat, Schema)
allSubtrees s@(s1 .+. s2) zs =
  let h = schemaHeight s
      zs' = allSubtrees s1 zs
  in  allSubtrees s2 zs' `snoc` (h, s)
allSubtrees s zs = zs `snoc` (0, s)

-- The same as allSubtrees, but calculate tree height along walking the tree,
-- instead of calling 'schemaHeight' each time. Also returns maximum tree
-- height.
export
allSubtrees' : Schema -> List (Nat, Schema) -> (Nat, List (Nat, Schema))
allSubtrees' s@(sl .+. sr) zs =
  let (hl, zs') = allSubtrees' sl zs
      (hr, zs'') = allSubtrees' sr zs'
      h = max hl hr + 1
  in  (h, zs'' `snoc` (h, s))
allSubtrees' s zs = (0, zs `snoc` (0, s))

-- Add x to the vector element with index m.
addToLevel : (m : Nat) -> (x : a) -> (n ** Vect n (List a)) -> (n' ** Vect n' (List a))
addToLevel m x (n ** vs) =
  let fm = natToFin2 m n
      vs' = padEmpty m vs
      xs = index fm vs'
  in  (_ ** replaceAt fm (xs `snoc` x) vs')

-- Store all Schema subtrees in a vector indexed by subtree height.
export
allSubtrees2 : Schema -> (n ** Vect n (List Schema)) -> (Nat, (n ** Vect n (List Schema)))
allSubtrees2 s@(sl .+. sr) acc =
  let (hl, acc') = allSubtrees2 sl acc
      (hr, acc'') = allSubtrees2 sr acc'
      height = max hl hr + 1
  in (height, addToLevel height s acc'')
allSubtrees2 s acc = (0, addToLevel 0 s acc)

-- By knowing schema height (e.g. 2) and resulting vector length (e.g. 3),
-- idris can't solve equation to find hole ?n satisfying
--
--          3 = maximum 2 ?n
--
-- probably, because it can't pattern match on unknown value ?n. But anyway
-- such expression is incorrect: vector length is known (here - 3) and in fact
-- there's no equation at all, just a condition, but i don't know how to
-- express a condition. If i specify ?n explicitly, then everything will work,
-- but that has no sense.
allSubtrees2' : (scm : Schema) -> {n : Nat} -> Vect (maximum (S (schemaHeight scm)) n) (List Schema) -> (Nat, Vect (maximum (S (schemaHeight scm)) n) (List Schema))

-- But all this does not needed, in fact, to implement Search..

export
Eq Schema where
  SInt == SInt = True
  SChar == SChar = True
  SString == SString = True
  (l1 .+. r1) == (l2 .+. r2) = (l1 == l2) && (r1 == r2)
  _ == _ = False

-- Type level schema equality.
public export
data EqSchema : Schema -> Schema -> Type where
  SameSchema : (scm : Schema) -> EqSchema scm scm

-- Proof of schema equality at type level.
export
total maybeEqualSchema : (scm1 : Schema) -> (scm2 : Schema) -> Maybe (EqSchema scm1 scm2)
maybeEqualSchema SInt SInt = Just (SameSchema SInt)
maybeEqualSchema SChar SChar = Just (SameSchema SChar)
maybeEqualSchema SString SString = Just (SameSchema SString)
maybeEqualSchema (l1 .+. r1) (l2 .+. r2) = do
  (SameSchema l) <- maybeEqualSchema l1 l2
  (SameSchema r) <- maybeEqualSchema r1 r2
  pure (SameSchema (l .+. r))
maybeEqualSchema _ _ = Nothing

-- Value-level implementation.

-- Return supplied value with Schema scm1, if both schemas are the same. Well,
-- this will not be needed, probably, if Schema has Eq instance..
matchSchema : (scm1 : Schema) -> (scm2 : Schema) -> SchemaType scm1 -> Maybe (SchemaType scm2)
matchSchema scm1 scm2 v = (\(SameSchema _) => v) <$> maybeEqualSchema scm1 scm2

-- Find all values with Schema scm2 in value with Schema scm1, if any.
-- (implementation).
findSubtreeValuesV' : (scm1 : Schema) -> (scm2 : Schema)
   -> (scm2Height : Nat)
   -> SchemaType scm1
   -> (Nat, List (SchemaType scm2))
findSubtreeValuesV' scm1@(sl .+. sr) scm2 scm2Height (x, y) =
  let (hl, left)  = findSubtreeValuesV' sl scm2 scm2Height x
      (hr, right) = findSubtreeValuesV' sr scm2 scm2Height y
      myHeight = maximum hl hr + 1
  in  (myHeight,
        case compare myHeight scm2Height of
             LT => []
             GT => left ++ right
             EQ => maybe [] singleton (matchSchema (sl .+. sr) scm2 (x, y))
      )
findSubtreeValuesV' scm1 scm2 Z     x =
  (0, maybe [] singleton (matchSchema scm1 scm2 x))
findSubtreeValuesV' _    _    (S _) _ = (0, [])

-- Find all values with Schema scm2 in value with Schema scm1, if any. (API)
export
findSubtreeValuesV
    : (scm1 : Schema) -> (scm2 : Schema)
    -> SchemaType scm1 -> List (SchemaType scm2)
findSubtreeValuesV scm1 scm2 = snd . findSubtreeValuesV' scm1 scm2 (schemaHeight scm2)


-- Type-level implementations.

-- Only full Schema is recorded in type. Subtree Schema is recorded in value.
data SchemaSubtree1 : (full : Schema) -> Type where
  JustSchema1 : (k : Schema) -> SchemaSubtree1 k
  LeftSubtree1 : {k : Schema} -> SchemaSubtree1 l -> SchemaSubtree1 (l .+. k)
  RightSubtree1 : {k : Schema} -> SchemaSubtree1 r -> SchemaSubtree1 (k .+. r)

total subtreeSchema1 : SchemaSubtree1 full -> Schema
subtreeSchema1 (JustSchema1 scm) = scm
subtreeSchema1 (LeftSubtree1 l) = subtreeSchema1 l
subtreeSchema1 (RightSubtree1 r) = subtreeSchema1 r

-- Extract value matching particular full Schema's subtree from original value
-- of type (SchemaType full)
total subtreeValue1
    : SchemaType full
    -> (sub : SchemaSubtree1 full)
    -> SchemaType (subtreeSchema1 sub)
subtreeValue1 x (JustSchema1 _) = x
subtreeValue1 (x, _) (LeftSubtree1 l)  = subtreeValue1 x l
subtreeValue1 (_, y) (RightSubtree1 r) = subtreeValue1 y r

-- Find all subtrees with Schema sub in original Schema full.
total findSubtrees1
    : (full : Schema) -> (sub : Schema)
    -> Nat -- Height of original sub Schema.
    -> (Nat, List (SchemaSubtree1 full))
findSubtrees1 (sl .+. sr) sub subHeight =
  let (hl, left) = findSubtrees1 sl sub subHeight
      (hr, right) = findSubtrees1 sr sub subHeight
      myHeight = maximum hl hr + 1
  in  (myHeight
      , case compare myHeight subHeight of
             LT => []
             GT => map LeftSubtree1 left ++ map RightSubtree1 right
             -- Note here, because subtree's Schema sub is not recorded in
             -- SchemaSubtree1 type, i don't need to assert Schema equality at
             -- type-level and regular value-level comparison is enough.
             EQ => if (sl .+. sr) == sub
                      then [JustSchema1 (sl .+. sr)]
                      else []
      )
findSubtrees1 full sub Z =
  -- Note here, because subtree's Schema sub is not recorded in SchemaSubtree1
  -- type, i don't need to assert Schema equality at type-level and regular
  -- value-level comparison is enough.
  (0, if full == sub then [JustSchema1 full] else [])
findSubtrees1 _    _    (S _) = (0, [])

findSubtreeValues1
      : (full : Schema) -> (sub : Schema)
      -> SchemaType full -> List (SchemaType sub)
findSubtreeValues1 full sub val =
  let h = schemaHeight sub
  in  case findSubtrees1 full sub h of
           (_, a :: acc) => let w = subtreeValue1 val a
                                -- I can't implement this, because here i have
                                -- a list 'acc' of schema subtrees
                                --
                                --      List (SchemaSubtree1 full)
                                --
                                -- and subtreeValue1 returns values of type
                                --
                                --      SchemaType (subtreeSchema1 sub)
                                --
                                -- but i can't prove, that for all elements of list 'acc' function subtreeSchema1
                                -- will return the same Schema. Example:
                                --
                                --      :t (RightSubtree1 {k = SInt} (JustSchema1 SString))
                                --      RightSubtree1 (JustSchema1 SString) : SchemaSubtree1 (SInt .+. SString)
                                --      :t (LeftSubtree1 {k = SString} (JustSchema1 SInt))
                                --      LeftSubtree1 (JustSchema1 SInt) : SchemaSubtree1 (SInt .+. SString)
                                --
                                -- SchemaSubtree1 type is the same, but underlying subtree schema is obviously different.
                                --
                                -- I.e. i can't implement following call:
                                --ws = map (subtreeValue1 val) acc
                            in  ?wrong1
           _ => []


-- Here i record both subtree schema and full schema in type.
public export
data SchemaSubtree : (full : Schema) -> (sub : Schema) -> Type where
  JustSchema : (sub : Schema) -> SchemaSubtree sub sub
  LeftSubtree  : {k : Schema} -> SchemaSubtree l sub -> SchemaSubtree (l .+. k) sub
  RightSubtree : {k : Schema} -> SchemaSubtree r sub -> SchemaSubtree (k .+. r) sub

-- I don't need subtreeSchema anymore, because subtree schema is recorded in
-- type.

export
total subtreeValue : SchemaType full -> SchemaSubtree full sub -> SchemaType sub
subtreeValue x (JustSchema _) = x
subtreeValue (x, _) (LeftSubtree l)  = subtreeValue x l
subtreeValue (_, y) (RightSubtree r) = subtreeValue y r

-- The same as 'findSubtrees1', but for 'SchemaSubtree'.
export
total findSubtrees
        : (full : Schema) -> (sub : Schema)
        -> (subHeight : Nat) -- Height of original sub Schema.
        -> (Nat, List (SchemaSubtree full sub))
findSubtrees (sl .+. sr) sub subHeight =
  let (hl, left) = findSubtrees sl sub subHeight
      (hr, right) = findSubtrees sr sub subHeight
      myHeight = maximum hl hr + 1
  in  (myHeight
      , case compare myHeight subHeight of
             LT => []
             GT => map LeftSubtree left ++ map RightSubtree right
             -- Note here, that because subtree Schema sub is now recorded in
             -- SchemaSubtree type, in order to use JustSchema constructor i
             -- need to prove, that full and sub schemas are equal at type
             -- level.
             EQ => case maybeEqualSchema (sl .+. sr) sub of
                        Just (SameSchema (l .+. r)) => [JustSchema (l .+. r)]
                        _ => []
             -- Alternatively, i may implement schema equality inline without
             -- 'EqSchema' type. But the 'EqSchema' implementation is more
             -- clear, probably.
             {-
             EQ => case maybeJustSubtree (sl .+. sr) sub of
                        Just sub => [sub]
                        _ => []
                        -}
      )
  where
    -- Return subtree schema as a subtree of itself, if full is equal to sub.
    maybeJustSubtree : (full : Schema) -> (sub : Schema) -> Maybe (SchemaSubtree full sub)
    maybeJustSubtree SInt SInt = Just (JustSchema SInt)
    maybeJustSubtree SChar SChar = Just (JustSchema SChar)
    maybeJustSubtree SString SString = Just (JustSchema SString)
    maybeJustSubtree (l1 .+. r1) (l2 .+. r2) = do
      (JustSchema l) <- maybeJustSubtree l1 l2 | _ => Nothing
      (JustSchema r) <- maybeJustSubtree r1 r2 | _ => Nothing
      pure (JustSchema (l .+. r))
    maybeJustSubtree _ _ = Nothing
findSubtrees full sub Z =
  (0,
      -- Note here, that because subtree Schema sub is now recorded in
      -- SchemaSubtree type, in order to use JustSchema constructor i need
      -- to prove, that full and sub schemas are equal at type level.
      case maybeEqualSchema full sub of
           Nothing => []
           Just (SameSchema scm) => [JustSchema scm]
  )
findSubtrees _    _    (S _) = (0, [])

-- Find all values with subtree Schema sub contained in a single value with
-- Schema full.
export
total findSubtreeValues
        : (full : Schema) -> (sub : Schema)
        -> SchemaType full -> List (SchemaType sub)
findSubtreeValues full sub val =
  let h = schemaHeight sub
      (_, acc) = findSubtrees full sub h
      -- And now, unlike findSubtreeValues1, all is fine: i have a list 'acc'
      -- of schema subtrees
      --
      --        List (SchemaSubtree full sub)
      --
      -- and because subtree schema is recorded in type, it's known to be the
      -- same for all list elements. Thus, i can just use map to find
      -- corresponding values.
  in  map (subtreeValue val) acc

-- Find in a list comparison function corresponding to the schema.
findCmp
      : (scm : Schema)
      -> List (scm' : Schema ** SchemaType scm' -> SchemaType scm' -> Bool)
      -> Maybe (SchemaType scm -> SchemaType scm -> Bool)
findCmp scm = foldr go Nothing
  where
    go : (scm' : Schema ** SchemaType scm' -> SchemaType scm' -> Bool)
        -> Maybe (SchemaType scm -> SchemaType scm -> Bool)
        -> Maybe (SchemaType scm -> SchemaType scm -> Bool)
    go (scm' ** f) z =
      case maybeEqualSchema scm scm' of
           Just (SameSchema l) => Just f
           Nothing => z

-- Find (in a list) or build (from component functions from a list) comparison
-- function corresponding to the schema.
export
buildMatcher
      : (scm : Schema)
      -> SchemaType scm
      -> List (scm' : Schema ** SchemaType scm' -> SchemaType scm' -> Bool)
      -> SchemaType scm -> Bool
buildMatcher SInt x funcs = maybe (== x) ($ x) (findCmp SInt funcs)
buildMatcher SChar x funcs = maybe (== x) ($ x) (findCmp SChar funcs)
buildMatcher SString str funcs = maybe (isInfixOf str) ($ str) (findCmp SString funcs)
buildMatcher scm@(l .+. r) (lval, rval) funcs =
  maybe rec ($ (lval, rval)) (findCmp scm funcs)
  where
    rec : (SchemaType l, SchemaType r) -> Bool
    rec = let lcmp = buildMatcher l lval funcs
              rcmp = buildMatcher r rval funcs
          in  \(x, y) => lcmp x && rcmp y

