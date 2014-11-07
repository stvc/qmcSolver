import String (toInt, split, show, trim, fromList)
import Graphics.Input (Input, input)
import Graphics.Input.Field as Field
import List (filterMap)
import Maybe (Maybe(..))
import Text
import Window

-- Types
type Minterm = Int
type Implicant = [Maybe Bool]


-- Signals
minTermString : Input Field.Content
minTermString = input Field.noContent

minTerms : Signal [Minterm]
minTerms = lift (sort << uniques [] << stringToListOfNums) minTermString.signal

dontCareString : Input Field.Content
dontCareString = input Field.noContent

dontCares' : Signal [Minterm]
dontCares' = lift (sort << uniques [] << stringToListOfNums) dontCareString.signal

dontCares : Signal [Minterm]
dontCares = uniques <~ minTerms ~ dontCares'

justs = filterMap identity

-- this function might need a bit of explanation to understand what is happening.
-- First: it takes a list as a key, and another list to filter
-- it removes all occurences of any elements in the first list from the second,
-- and also removes all duplicates that occure within the second list itself
-- the result is a list of only new, unique values
uniques : [Int] -> [Int] -> [Int]
uniques k = let
        removeDupes x xs = if (filter ((==) x) (k ++ xs)) == [] then x :: xs else xs
    in foldr removeDupes []

stringToListOfNums : Field.Content -> [Int]
stringToListOfNums = justs << map (toInt << trim) << split "," << .string

display : (Int,Int) -> Element -> Element -> [Int] -> [Int] -> Element
display (x,y) mtf dcf mt dc = above
    (color darkCharcoal <| container x 80 middle <| centered <| bold
            <| Text.height 30 <| Text.color lightGrey <| toText "Quine-McCluskey Solver")
    (color grey <| container x (y-80) midTop <| flow down
        [   spacer x 10
        ,   container x 65 midTop <| above
                (container 350 32 middle mtf)
                (container 350 32 middle dcf)
        ,   container x 30 midTop <| centered <| typeface ["Times New Roman" , "serif"]
                <| Text.height 20 <| bold <| Text.color darkCharcoal <| toText
                <| solve mt dc
        ,   container x 300 bottomLeft <| leftAligned <| Text.color charcoal
                <| monospace <| toText <| " DEBUG INFO:\n  Minterms: " ++ (show mt)
                    ++ "\n  DontCares: " ++ (show dc)
                    ++ "\n  NumInputs: " ++ (show <| getNumInputs (dc ++ mt))
                    ++ "\n  Implicants: " ++ (show <| mintermsToImplicants (dc ++ mt))
                    ++ "\n  Back to minterms: " ++ (show <| concatMap implicantToMinterms <| mintermsToImplicants (dc ++ mt))
                    ++ "\n  Reduce test: " ++ (show <| buildReducedImplicants <| mintermsToImplicants (dc ++ mt))
        ,   container x 30 middle <| centered <| Text.color lightCharcoal
                <| toText "Written by Steve Cain"
        ]
    )

main : Signal Element
main = display <~ Window.dimensions ~
    (color white <~ (Field.field Field.defaultStyle minTermString.handle identity "MinTerms" <~ minTermString.signal)) ~
    (color white <~ (Field.field Field.defaultStyle dontCareString.handle identity "'Dont Care' Terms" <~ dontCareString.signal)) ~
    (minTerms) ~ (dontCares)

getNumInputs : [Minterm] -> Int
getNumInputs l = case l of
    []        -> 0
    otherwise -> ceiling <| logBase 2 <| toFloat <| (+) 1 <| maximum l

-- solve takes a list of minterms, and a list of don't care terms
-- it then combines them and converts them
solve : [Minterm] -> [Minterm] -> String
solve _ _ = "tmp"


-- Converts a minterm to an Implicant
--   The first parameter is the size of the implicant (the number of inputs)
mintermToImplicant : Int -> Minterm -> Implicant
mintermToImplicant sz term = let
        convert s x = if s < 0
            then []
            else let y = x // (2^(s))
                in y :: (convert (s-1) (x - y*(2^s)))
        convert' n = case n of
            0 -> Just False
            1 -> Just True
    in map convert' <| convert (sz - 1) term

mintermsToImplicants : [Minterm] -> [Implicant]
mintermsToImplicants ts = map (mintermToImplicant (getNumInputs ts)) ts

implicantToMinterms : Implicant -> [Minterm]
implicantToMinterms = snd << foldr implicantToMinterms' (0,[0])

implicantToMinterms' : Maybe Bool -> (Int, [Minterm]) -> (Int, [Minterm])
implicantToMinterms' input (pow, terms) = let
        fal  = terms
        tru  = map ((+) (2 ^ pow)) terms
        both = fal ++ tru
    in case input of
        Just False -> (pow + 1, fal)
        Just True  -> (pow + 1, tru)
        Nothing    -> (pow + 1, both)

offByOne : Implicant -> Implicant -> Bool
offByOne xs ys = let
        comb (x,y) acc = if x == y then acc else acc+1
    in ((==) 1) <| foldl comb 0 <| zip xs ys

combineImplicants : Implicant -> Implicant -> Maybe Implicant
combineImplicants a b = let
        comb (x,y) acc = if x == y then x::acc else Nothing::acc
        combineImplicants' xs ys = foldr comb [] <| zip xs ys
    in if offByOne a b then Just (combineImplicants' a b) else Nothing

-- the first parameter is the minterm, and the second is the reduced implicant
covers : Implicant -> Implicant -> Bool
covers mt imp = let
        l = zip mt imp
        f (t,i) acc = case i of
            Nothing   -> acc
            otherwise -> if t == i then acc else False
    in foldl f True l

buildReducedImplicants : [Implicant] -> [Implicant]
buildReducedImplicants impls = let
        buildReducedImplicants' (rImpls, nrImpls) = case rImpls of
            []  -> nrImpls
            otherwise -> buildReducedImplicants' (reduce rImpls) ++ nrImpls
    in buildReducedImplicants' (impls, [])

-- reduces a list of implicants one level. returns a tuple of two lists.
-- the first list is of reduced Implicants, the second is of unreducable implicants
reduce : [Implicant] -> ([Implicant], [Implicant])
reduce impl = let
        reduce' t (rs, nrs, orig) = if (any (covers t) rs)
            then (rs, nrs, orig)
            else case justs (map (combineImplicants t) orig) of
                [] -> (rs, t::nrs, orig)
                xs -> (xs ++ rs, nrs, orig)
        (fi,se,_) = foldl reduce' ([],[],impl) impl
    in (fi,se)

