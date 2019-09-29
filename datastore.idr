module Main
  
import Data.Vect

------------------------
--- replWith example ---
------------------------
 
sumInputs : Integer -> String -> Maybe (String, Integer)
sumInputs tot inp = 
  let val = cast inp
  in if val < 0
     then Nothing
     else let newVal = tot + val
          in Just ("Subtotal: " ++ show newVal ++ "\n", newVal)
    
main' : IO ()
main' = replWith 0 "Value: " sumInputs


-----------------
--- Datastore ---
-----------------
  
data DataStore : Type where
  MkData : (size : Nat) -> (items : Vect size String) -> DataStore
  
data Command = Add String | Get Integer | Quit | Size | Search String

size : DataStore -> Nat
size (MkData size' _) = size'

items : (store : DataStore) -> Vect (size store) String
items (MkData _ items') = items'

addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) item = MkData _ (f items)
  where
    f : Vect old String -> Vect (S old) String
    f [] = [item]
    f (x :: xs) = x :: f xs

searchStore : DataStore -> (val : String) -> String
searchStore (MkData _ store) val = f store
  where
    f : Vect m String -> String
    f {m = Z} [] = ""
    f {m = S l} (x :: xs) = if val `isInfixOf` x then show l ++ ": " ++ x ++ "\n" ++ f xs else f xs

parseCommand : (cmd : String) -> (args : String) -> Maybe Command
parseCommand "add" str = Just $ Add str
parseCommand "search" val = Just $ Search val
parseCommand "get" val = if all isDigit (unpack val) then Just (Get (cast val)) else Nothing
parseCommand "quit" "" = Just Quit
parseCommand "size" "" = Just Size
parseCommand _ _ = Nothing

parse : (input : String) -> Maybe Command
parse input = case span (/= ' ' ) input of
                   (cmd, args) => parseCommand cmd (ltrim args)

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = 
  let storeItems = items store 
  in (case integerToFin pos (size store) of
           Nothing => Just ("Out of range\n", store)
           (Just id) => Just (index id storeItems , store))

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp = case parse inp of
                              Nothing => Nothing
                              (Just Quit) => Nothing
                              (Just (Add item)) =>
                                Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
                              (Just (Get x)) => getEntry x store
                              (Just Size) => Just ("Store size: " ++ show (size store) ++ "\n", store)
                              (Just (Search val)) => Just (searchStore store val, store)
sto : DataStore
sto = MkData 3 ["One", "Two", "Three"]

res : String
res = searchStore sto "T"

main : IO ()
main = replWith (MkData _ []) "Command: " processInput

