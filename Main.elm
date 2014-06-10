import String (toInt, split, show, trim, fromList)
import Graphics.Input (Input, input)
import Graphics.Input.Field as Field
import Maybe (Just, Nothing, justs)
import Window

minTermString : Input Field.Content
minTermString = input Field.noContent

minTerms : Signal [Int]
minTerms = lift (sort . uniques [] . stringToListOfNums) minTermString.signal

dontCareString : Input Field.Content
dontCareString = input Field.noContent

dontCares' : Signal [Int]
dontCares' = lift (sort . uniques [] . stringToListOfNums) dontCareString.signal

dontCares : Signal [Int]
dontCares = uniques <~ minTerms ~ dontCares'

-- this function might need a bit of explaination to understand what is happening.
-- First: it takes a list as a key, and another list to filter
-- it removes all occurences of any elements in the first list from the second,
-- and also removes all duplicates that occure within the second list itself
-- the result is a list of only new, unique values
uniques : [Int] -> [Int] -> [Int]
uniques k = let
    removeDupes x xs = if (filter ((==) x) (k ++ xs)) == [] then x :: xs else xs in
    foldr removeDupes []

stringToListOfNums : Field.Content -> [Int]
stringToListOfNums = justs . map (toInt . trim) . split "," . .string

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
                    ++ "\n  Sorted Binary: " ++ (show <| map (map fromList) <| partitionByNumOnes <| decToListBinChar (getNumInputs (dc ++ mt)) (dc ++ mt))
                    ++ "\n  Off by one test: " ++ (show <| isOffByOneTest)
                    ++ "\n  Replacement Test: " ++ (show <| replaceDifferencesTest.exp)
                    ++ "\n  0100 to implicant: " ++ (show <| charsToImplicant ['0','1','0','0'])
        ,   container x 30 middle <| centered <| Text.color lightCharcoal
                <| toText "Written by Steven Cain"
        ]
    )

main : Signal Element
main = display <~ Window.dimensions ~
    (Field.field Field.defaultStyle minTermString.handle id "MinTerms" <~ minTermString.signal) ~
    (Field.field Field.defaultStyle dontCareString.handle id "'Dont Care' Terms" <~ dontCareString.signal) ~
    (minTerms) ~ (dontCares)

getNumInputs : [Int] -> Int
getNumInputs l = case l of
    []        -> 0
    otherwise -> ceiling <| logBase 2 <| toFloat <| (+) 1 <| maximum l

-- solve takes a list of minterms, and a list of don't care terms
-- it then combines them and converts them
solve : [Int] -> [Int] -> String
solve _ _ = "tmp"
--solve mt dc = let
--        terms = mt ++ dc

-- takes a bit size and a list of dec values and converts them to a list of lists of characters
decToListBinChar : Int -> [Int] -> [[Char]]
decToListBinChar sz = let
        convert s x = if s < 0
            then []
            else let y = x `div` (2^(s))
                in y :: (convert (s-1) (x - y*(2^s)))
        convert' n = case n of
            0 -> '0'
            1 -> '1'
    in map (map convert' . convert (sz - 1))

partitionByNumOnes : [[Char]] -> [[[Char]]]
partitionByNumOnes = let
        countOnes = length . filter ((==) '1')
        partByOnes n = partition ((==) n . countOnes)
        partitionByNumOnes' n l = case l of
            [] -> []
            xs -> let
                    (fpbo, spbo) = partByOnes n xs
                in fpbo :: partitionByNumOnes' (n+1) spbo
    in partitionByNumOnes' 0

type Implicant = { exp : [Char], used : Bool, terms : [Int] }

charsToImplicant : [Char] -> Implicant
charsToImplicant cs = let
        t = fst <| foldr (\ c (s, d) -> if c == '1' then (s + 2^d, d+1) else (s, d+1)) (0,0) <| cs
    in { exp = cs, used = False, terms = [t] }

-- takes two lists of implicants (the first with n 1's and the second with
-- (n+1) 1's. it returns a tuple of two lists of implicants. the first being
-- the two inputs concatenated together with their 'used' field set to true if
-- they were used, and the second being a list of reduced implicants
generateReducedImplicants : [Implicant] -> [Implicant] -> ([Implicant], [Implicant])
generateReducedImplicants a b = let
        usedTerms = []
        newTerms  = []
    in (usedTerms, newTerms)

{-
generateMatchingImplicants : [Implicant] -> Implicant -> (Implicant, [Implicant])
generateMatchingImplicants bs i = let
        newTerms = foldl (\ x a -> if (isO -- shit wont work, i need to keep track of used terms in bs
        newImplicant = if (length newTerms) == 0 then i else {i | used <- True}
    in (newImplicant, newTerms)

-}

isOffByOneTest = isOffByOne (charsToImplicant ['0','0']) (charsToImplicant ['1','1'])
replaceDifferencesTest = replaceDifferences (charsToImplicant ['1','0']) (charsToImplicant ['0','0'])

isOffByOne : Implicant -> Implicant -> Bool
isOffByOne a b = let
        m = a.exp
        n = b.exp
        isOffByOne' (x,y) c = if x == y then c else c+1
    in if (length m) /= (length n) then False
        else (==) 1 <| foldl isOffByOne' 0 <| zip m n

replaceDifferences : Implicant -> Implicant -> Implicant
replaceDifferences a b = let
        m = a.exp
        n = b.exp
        replaceDifferences' (x,y) acc = if x == y then x :: acc else '-' :: acc
    in charsToImplicant <| foldr replaceDifferences' [] <| zip m n
