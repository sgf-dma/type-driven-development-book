
module Schema

import Data.String
import Data.Vect

import Utils

export infixr 5 .+.

public export
data Schema = SString
            | SInt
            | (.+.) Schema Schema

export
displaySchema : (parens : Bool) -> Schema -> String
displaySchema _ SInt = "Int"
displaySchema _ SString = "String"
displaySchema parens ((.+.) s1 s2) =
  showParens parens (displaySchema True s1 ++ " " ++ displaySchema False s2)
  where
    showParens : Bool -> String -> String
    showParens True input = "(" ++ input ++ ")"
    showParens False input = input

closeParen : (String -> Maybe (a, String)) -> String -> Maybe (a, String)
closeParen parse input = do
  (x, rest) <- parse input
  let rest' = ltrim rest    -- Accept ')' with leading spaces.
  case strM rest' of
       StrCons ')' rest2 => pure (x, rest2)
       _ => Nothing

-- Parse parenthesis around expression parsed by another parser 'parse'.
export
parseParens : (parse : String -> Maybe (a, String)) -> (input : String) -> Maybe (a, String)
parseParens parse input =
  let input' = ltrim input
  in  case strM input' of
           StrCons '(' rest => closeParen parse rest
           _ => parse input

export
parseSchemaPrefix : String -> Maybe (Schema, String)
parseSchemaPrefix input = do
  -- I accept tokens with leading spaces, so `ltrim` first.
  (s1, rest) <- case span (\c => c /= ' ' && c /= '(' && c /= ')') (ltrim input) of
       ("String", rest) => pure (SString, rest)
       ("Int", rest) => pure (SInt, rest)
       ("", rest) => case strM rest of
            -- I may handle spaces explicitly or i may just skip them as
            -- "leading spaces" with `ltrim`, as i did above.
            --StrCons ' ' rest' => parseSchemaPrefix rest' -- Right associativity.
            StrCons '(' rest' => closeParen parseSchemaPrefix rest'
            StrCons ')' _ => Nothing
            _ => Nothing
       _ => Nothing
  case parseSchemaPrefix rest of
       Nothing => pure (s1, rest)
       Just (s2, rest') => pure (s1 .+. s2, rest')

export
parseSchema : String -> Maybe Schema
parseSchema s = case parsePrefix s of
                     Nothing => Nothing
                     Just (s1, "") => Just s1
                     Just (s1, rest) => case parseSchema (ltrim rest) of
                                             Nothing => Nothing
                                             Just s2 => Just (s1 .+. s2)
  where
    parsePrefix : String -> Maybe (Schema, String)
    parsePrefix input =
      case span (/= ' ') input of
           ("String", rest) => Just (SString, rest)
           ("Int", rest) => Just (SInt, rest)
           _ => Nothing

public export
TypeSchema : Type -> Maybe Schema
TypeSchema Int = Just SInt
TypeSchema String = Just SString
TypeSchema (a, b) = (.+.) <$> TypeSchema a <*> TypeSchema b
TypeSchema _ = Nothing

public export
SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (a .+. b) = (SchemaType a, SchemaType b)

export
display : {scm : Schema} -> SchemaType scm -> String
display {scm = SInt} x = show x
display {scm = SString} x = show x
display {scm = (.+.) a b} (x, y) = "(" ++ display x ++ ", " ++ display y ++ ")"

parsePrefix : (scm : Schema) -> String -> Maybe (SchemaType scm, String)
parsePrefix SInt input =
  case span isDigit input of
       ("", _) => Nothing
       (s, rest) => Just (cast s, ltrim rest)
parsePrefix SString input = getQuoted (unpack input)
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"' :: rs) = 
       case span (/= '"') rs of
            (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
            _ => Nothing
    getQuoted _ = Nothing
parsePrefix ((.+.) a b) input =
  case parsePrefix a input of
       Nothing => Nothing
       Just (left, rr) => case parsePrefix b rr of
                               Nothing => Nothing
                               Just (right, rest) => Just ((left, right), rest)

-- parsePrefix' requires one or more spaces between elements. Also, as a
-- side-effect, it leaves trailing spaces as is. Thus, to use it, i need to
-- remove trailing spaces in parseBySchema.
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
parsePrefix' ((.+.) a b) input =
  case parsePrefix' a input of
       Nothing => Nothing
       Just (left, rr) => case span (== ' ') rr of
                               (_, "") => Nothing
                               ("", _) => Nothing
                               (l, rr') => case parsePrefix' b (ltrim rr') of
                                                Nothing => Nothing
                                                Just (right, rest) => Just ((left, right), rest)

export
parseBySchema : (scm : Schema) -> String -> Maybe (SchemaType scm)
parseBySchema scm input =
  case parsePrefix scm input of
       Just (res, "") => Just res
       _ => Nothing

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

-- Type level schema equality.
data EqSchema : Schema -> Schema -> Type where
  SameSchema : (scm : Schema) -> EqSchema scm scm

-- Proof of schema equality at type level.
total maybeEqualSchema : (scm1 : Schema) -> (scm2 : Schema) -> Maybe (EqSchema scm1 scm2)
maybeEqualSchema SInt SInt = Just (SameSchema SInt)
maybeEqualSchema SString SString = Just (SameSchema SString)
maybeEqualSchema (l1 .+. r1) (l2 .+. r2) =
  case maybeEqualSchema l1 l2 of
       Nothing => Nothing
       Just (SameSchema l) => case maybeEqualSchema r1 r2 of
                      Nothing => Nothing
                      Just (SameSchema r) => Just (SameSchema (l .+. r))
maybeEqualSchema _ _ = Nothing

-- Value-level implementation.

-- Return supplied value with Schema scm1, if both schemas are the same. Well,
-- this will not be needed, probably, if Schema has Eq instance..
matchSchema : (scm1 : Schema) -> (scm2 : Schema) -> SchemaType scm1 -> Maybe (SchemaType scm2)
matchSchema scm1 scm2 v = (\(SameSchema _) => v) <$> maybeEqualSchema scm1 scm2

-- Find all values with Schema scm2 in value with Schema scm1, if any.
-- (implementation).
findSubtreeValuesV' : (scm1 : Schema) -> (scm2 : Schema)
   -> Nat
   -> SchemaType scm1
   -> (Nat, List (SchemaType scm2))
findSubtreeValuesV' scm1@(sl .+. sr) scm2 height (x, y) =
  let (hl, left)  = findSubtreeValuesV' sl scm2 height x
      (hr, right) = findSubtreeValuesV' sr scm2 height y
      myHeight = maximum hl hr + 1
  in  (myHeight,
        case compare myHeight height of
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
findSubtreeValuesV scm1 scm2 val =
  snd $ findSubtreeValuesV' scm1 scm2 (schemaHeight scm2) val


-- Type-level implementations.

-- Only full Schema is recorded in type. Subtree Schema is recorded in value.
data SchemaSubtree1 : Schema -> Type where
  JustSchema1 : (k : Schema) -> SchemaSubtree1 k
  LeftSubtree1 : {k : Schema} -> SchemaSubtree1 l -> SchemaSubtree1 (l .+. k)
  RightSubtree1 : {k : Schema} -> SchemaSubtree1 r -> SchemaSubtree1 (k .+. r)

total subtreeSchema1 : SchemaSubtree1 s -> Schema
subtreeSchema1 (JustSchema1 scm) = scm
subtreeSchema1 (LeftSubtree1 l) = subtreeSchema1 l
subtreeSchema1 (RightSubtree1 r) = subtreeSchema1 r

-- Extract value matching particular Schema scm1 subtree from original value
-- with Schema scm1.
total subtreeValue1
    : SchemaType scm1
    -> (sub : SchemaSubtree1 scm1)
    -> SchemaType (subtreeSchema1 sub)
subtreeValue1 x (JustSchema1 _) = x
subtreeValue1 (x, _) (LeftSubtree1 l)  = subtreeValue1 x l
subtreeValue1 (_, y) (RightSubtree1 r) = subtreeValue1 y r

-- Value-level schema equality.
Eq Schema where
  SInt == SInt = True
  SString == SString = True
  (l1 .+. r1) == (l2 .+. r2) = (l1 == l2) && (r1 == r2)
  _ == _ = False

-- Find all subtrees with Schema scm2 in original Schema scm1.
total findSubtrees1
    : (scm1 : Schema) -> (scm2 : Schema)
    -> Nat -- Height of original scm2 Schema.
    -> (Nat, List (SchemaSubtree1 scm1))
findSubtrees1 (sl .+. sr) scm2 height =
  let (hl, left) = findSubtrees1 sl scm2 height
      (hr, right) = findSubtrees1 sr scm2 height
      myHeight = maximum hl hr + 1
  in  (myHeight
      , case compare myHeight height of
             LT => []
             GT => map LeftSubtree1 left ++ map RightSubtree1 right
             -- Note here, because subtree's Schema scm2 is not recorded in
             -- SchemaSubtree1 type, i don't need to assert Schema equality at
             -- type-level and regular value-level comparison is enough.
             EQ => if (sl .+. sr) == scm2
                      then [JustSchema1 (sl .+. sr)]
                      else []
      )
findSubtrees1 scm1 scm2 Z =
  -- Note here, because subtree's Schema scm2 is not recorded in SchemaSubtree1
  -- type, i don't need to assert Schema equality at type-level and regular
  -- value-level comparison is enough.
  (0, if scm1 == scm2 then [JustSchema1 scm1] else [])
findSubtrees1 _    _    (S _) = (0, [])

findSubtreeValues1
      : (scm1 : Schema) -> (scm2 : Schema)
      -> SchemaType scm1 -> List (SchemaType scm2)
findSubtreeValues1 scm1 scm2 val =
  let h = schemaHeight scm2
  in  case findSubtrees1 scm1 scm2 h of
           (_, a :: acc) => let w = subtreeValue1 val a
                                -- I can't implement this, because here i have
                                -- a list 'acc' of schema subtrees
                                --
                                --      List (SchemaSubtree1 scm1)
                                --
                                -- and subtreeValue1 returns values of type
                                --
                                --      SchemaType (subtreeSchema1 sub)
                                --
                                -- but i can't prove, that for all elements of
                                -- list 'acc' function subtreeSchema1 will
                                -- return the same Schema.
                                -- I.e. i can't implement following call:
                                --ws = map (subtreeValue1 val) acc
                            in  ?wrong1
           _ => []


-- Here i record both subtree schema and full schema in type.
export
data SchemaSubtree : Schema -> Schema -> Type where
  JustSchema : (sub : Schema) -> SchemaSubtree sub sub
  LeftSubtree  : {k : Schema} -> SchemaSubtree l sub -> SchemaSubtree (l .+. k) sub
  RightSubtree : {k : Schema} -> SchemaSubtree r sub -> SchemaSubtree (k .+. r) sub

-- I don't need subtreeSchema1 anymore, because subtree schema is recorded in
-- type.

export
total subtreeValue : SchemaType scm1 -> SchemaSubtree scm1 scm2 -> SchemaType scm2
subtreeValue x (JustSchema _) = x
subtreeValue (x, _) (LeftSubtree l)  = subtreeValue x l
subtreeValue (_, y) (RightSubtree r) = subtreeValue y r

-- The same as 'findSubtrees1', but for 'SchemaSubtree'.
export
total findSubtrees
        : (scm1 : Schema) -> (scm2 : Schema)
        -> Nat -- Height of original scm2 Schema.
        -> (Nat, List (SchemaSubtree scm1 scm2))
findSubtrees (sl .+. sr) scm2 height =
  let (hl, left) = findSubtrees sl scm2 height
      (hr, right) = findSubtrees sr scm2 height
      myHeight = maximum hl hr + 1
  in  (myHeight
      , case compare myHeight height of
             LT => []
             GT => map LeftSubtree left ++ map RightSubtree right
             -- Note here, that because subtree Schema scm2 is now recorded in
             -- SchemaSubtree type, in order to use JustSchema constructor i
             -- need to prove, that scm1 and scm2 schemas are equal at type
             -- level.
             EQ => case maybeEqualSchema (sl .+. sr) scm2 of
                        Just (SameSchema (l .+. r)) => [JustSchema (l .+. r)]
                        _ => []
      )
findSubtrees scm1 scm2 Z =
  (0,
      -- Note here, that because subtree Schema scm2 is now recorded in
      -- SchemaSubtree type, in order to use JustSchema constructor i need
      -- to prove, that scm1 and scm2 schemas are equal at type level.
      case maybeEqualSchema scm1 scm2 of
           Nothing => []
           Just (SameSchema scm) => [JustSchema scm]
  )
findSubtrees _    _    (S _) = (0, [])

export
total findSubtreeValues
        : (scm1 : Schema) -> (scm2 : Schema)
        -> SchemaType scm1 -> List (SchemaType scm2)
findSubtreeValues scm1 scm2 val =
  let h = schemaHeight scm2
      (_, acc) = findSubtrees scm1 scm2 h
      -- And now, unlike findSubtreeValues1, all is fine: i have a list 'acc'
      -- of schema subtrees
      --
      --        List (SchemaSubtree scm1 scm2)
      --
      -- and now subtree schema is recorded in type and it's known to be the
      -- same for all list elements. Thus, i can just use map to find
      -- corresponding values:
  in  map (subtreeValue val) acc

