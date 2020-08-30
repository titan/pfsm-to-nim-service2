module Pfsm.NimService2

import Data.Maybe
import Data.List
import Data.SortedMap
import Data.SortedSet
import Data.Strings
import Data.Vect
import System
import System.File

import Pfsm
import Pfsm.Analyser
import Pfsm.Checker
import Pfsm.Data
import Pfsm.Parser

indentDelta : Nat
indentDelta = 2

nimBuiltinTypes : List String
nimBuiltinTypes = [ "int" , "int8" , "int16" , "int32" , "int64" , "uint" , "uint8" , "uint16" , "uint32" , "uint64" , "float" , "floa t32" , "float64" , "true" , "false" , "char" , "string" , "cstring" ]

nimKeywords : List String
nimKeywords = [ "addr" , "and" , "as" , "asm" , "bind" , "block" , "break" , "case" , "cast" , "concept" , "const" , "continue" , "converter" , "defer" , "discard" , "distinct" , "div" , "do" , "elif" , "else" , "end" , "enum" , "except" , "export" , "finally" , "for" , "from" , "func" , "if" , "import" , "in" , "include" , "interface" , "is" , "isnot" , "iterator" , "let" , "macro" , "method" , "mixin" , "mod" , "nil" , "not" , "notin" , "object" , "of" , "or" , "out" , "proc" , "ptr" , "raise" , "ref" , "return" , "shl" , "shr" , "static" , "template" , "try" , "tuple" , "type" , "using" , "var" , "when" , "while" , "xor" , "yield" ]

primToNimType : PrimType -> String
primToNimType t
  = case t of
         PTBool   => "bool"
         PTByte   => "uint8"
         PTChar   => "char"
         PTShort  => "int16"
         PTUShort => "uint16"
         PTInt    => "int"
         PTUInt   => "uint"
         PTLong   => "int64"
         PTULong  => "uint64"
         PTReal   => "float64"
         PTString => "string"

toNimName : Name -> String
toNimName n
  = let n' = normalize n in
    if elemBy (==) n' nimKeywords
       then "my_" ++ n'
       else n'
  where
    mappings : List (String, String)
    mappings =  [ (" ", "_")
                , ("-", "_")
                , ("+", "plus")
                ]
    normalize : Name -> String
    normalize n = foldl (\acc, x => replaceAll (fst x) (snd x) acc) n mappings

toNimType : Tipe -> String
toNimType TUnit          = "void"
toNimType (TPrimType t)  = primToNimType t
toNimType (TList t)      = "seq[" ++ (toNimType t) ++ "]"
toNimType (TDict k v)    = "table[" ++ (primToNimType k) ++ "," ++ (toNimType v) ++ "]"
toNimType (TRecord n ts) = toNimName n
toNimType t@(TArrow a b) = case liftArrowParams t [] of
                                []      => toNimFuncType []           TUnit
                                x :: xs => toNimFuncType (reverse xs) x
                        where
                          liftArrowParams : Tipe -> List Tipe -> List Tipe
                          liftArrowParams (TArrow a b@(TArrow _ _)) acc = liftArrowParams b (a :: acc)
                          liftArrowParams (TArrow a b)              acc = b :: (a :: acc)
                          liftArrowParams _                         acc = acc

                          toNimFuncType : List Tipe -> Tipe -> String
                          toNimFuncType as r
                              = let args = join ", " (map (\(i, x) => "a" ++ (show i) ++ ": " ++ toNimType(x)) (enumerate as))
                                    ret  = toNimType r in
                                    "proc (" ++ args ++ "): " ++ ret

%hide Data.Vect.(::)

toNim : Fsm -> String
toNim fsm
  = join "\n\n" [ generateImports fsm
                , generateTypes
                , "var queue = initDeque[MessageFunc](8)"
                , generatePlayEvent fsm
                , generateToJson fsm
                , generateFromJson fsm
                , generateMainModule fsm
                ]
  where
    generateImports : Fsm -> String
    generateImports fsm
      = let name = toNimName fsm.name in
            join "\n" [ "import deques, json, logging, service2, strtabs, strutils"
                      , "import " ++ name
                      , "import " ++ name ++ "_delegates"
                      ]

    generateTypes : String
    generateTypes
      = join "\n" [ "type"
                  , (indent indentDelta) ++ "MessageFunc = proc (ctx: ServiceContext): void"
                  ]

    generatePlayEvent : Fsm -> String
    generatePlayEvent fsm
      = let es = fsm.events
            pre = camelize $ toNimName fsm.name in
            join "\n" [ "proc play_event(fsm: " ++ pre ++ "StateMachine, model: " ++ pre ++ "Model, context: ServiceContext, event: string, payload: StringTableRef): " ++ pre ++ "Model ="
                      , (indent indentDelta) ++ "case event:"
                      , generateEventHandlers (indentDelta * 2) es
                      , (indent (indentDelta * 2)) ++ "else:"
                      , generateDefaultEventHandler (indentDelta * 3)
                      ]
      where
        generateEventHandle : Nat -> Event -> String
        generateEventHandle idt evt@(MkEvent n ps _)
          = let srcs = [ (indent idt) ++ "of " ++ (show (toUpper (toNimName n))) ++ ":"
                       , generateFetchEventArgs (idt + indentDelta) ps
                       , generateEventCall (idt + indentDelta) evt
                       , generateQueueHandler (idt + indentDelta)
                       ] in
                join "\n" $ filter (\x => length x > 0) srcs
          where
            typeWrapper : String -> Tipe -> String
            typeWrapper s (TPrimType PTBool)   = s ++ ".parseBool"
            typeWrapper s (TPrimType PTByte)   = "cast[uint8](" ++ s ++ ".parseInt)"
            typeWrapper s (TPrimType PTShort)  = "cast[int16](" ++ s ++ ".parseInt)"
            typeWrapper s (TPrimType PTUShort) = "cast[uint16](" ++ s ++ ".parseUInt)"
            typeWrapper s (TPrimType PTInt)    = s ++ ".parseInt"
            typeWrapper s (TPrimType PTUInt)   = s ++ ".parseUInt"
            typeWrapper s (TPrimType PTLong)   = s ++ ".parseBiggestInt"
            typeWrapper s (TPrimType PTULong)  = s ++ ".parseBiggestUInt"
            typeWrapper s (TPrimType PTReal)   = s ++ ".parseFloat"
            typeWrapper s (TPrimType PTChar)   = "if len(" ++ s ++ ") > 0: " ++ s ++ "[0] else: '\\0'"
            typeWrapper s (TPrimType PTString) = s
            typeWrapper s (TList t)            = s ++ ".split(\",\").mapIt(" ++ (typeWrapper "it" t) ++ ")"
            typeWrapper s (TDict PTString t)   = s ++ ".split(\",\").mapIt(it.split(\":\")).mapIt((it[0], " ++ (typeWrapper "it[1]" t) ++ ")).newTable"
            typeWrapper s _                    = s

            generateFetchEventArg : Nat -> Parameter -> String
            generateFetchEventArg idt (n, t, _)
              = let lhs = (indent idt) ++ (toNimName n)
                    rhs = "payload.getOrDefault(\"" ++ (toUpper (toNimName n)) ++ "\")" in
                    lhs ++ " = " ++ (typeWrapper rhs t)

            generateFetchEventArgs : Nat -> List Parameter -> String
            generateFetchEventArgs idt ps
              = let args = map (generateFetchEventArg (idt + indentDelta)) ps in
                    if length args > 0
                       then (indent idt) ++ "let\n" ++ (join "\n" args)
                       else ""

            generateEventCall : Nat -> Event -> String
            generateEventCall idt (MkEvent n ps _)
              = (indent idt) ++ "result = " ++ (toNimName n) ++ "(" ++ (join ", " (map (\(n, _, _) => toNimName n) (("fsm", (TPrimType PTBool), Nothing) :: (("model", (TPrimType PTBool), Nothing) :: ps)))) ++ ")"

            generateQueueHandler : Nat -> String
            generateQueueHandler idt
              = join "\n" [ (indent idt) ++ "while len(queue) > 0:"
                          , (indent (idt + indentDelta)) ++ "let msgfun = queue.popFirst"
                          , (indent (idt + indentDelta)) ++ "msgfun(context)"
                          ]

        generateEventHandlers : Nat -> List Event -> String
        generateEventHandlers idt es
          = join "\n" $ map (generateEventHandle idt) es

        generateDefaultEventHandler : Nat -> String
        generateDefaultEventHandler idt
          = join "\n" [ (indent idt) ++ "info \"Unknown event: \" & event"
                      , (indent idt) ++ "info detail(payload, 2)"
                      , (indent idt) ++ "result = model"
                      ]

    generateToJson : Fsm -> String
    generateToJson fsm
      = let pre = camelize $ toNimName fsm.name in
            join "\n" [ "proc to_json(model: " ++ pre ++ "Model): JsonNode ="
                      , (indent indentDelta) ++ "result = newJObject()"
                      , generateModelToJson indentDelta fsm.model
                      ]
      where
        generateModelToJson : Nat -> List Parameter -> String
        generateModelToJson idt ps
          = join "\n" $ map (\(n, _, _) => (indent idt) ++ "result.add(" ++ (show n) ++ ", % model." ++ (toNimName n) ++ ")") ps

    generateFromJson : Fsm -> String
    generateFromJson fsm
      = let pre = camelize $ toNimName fsm.name in
            join "\n" [ "proc from_json(node: JsonNode): " ++ pre ++ "Model ="
                      , (indent indentDelta) ++ "result = new(" ++ pre ++ "Model)"
                      , generateModelFromJson indentDelta fsm.model
                      ]
      where
        typeWrapper : String -> Tipe -> String
        typeWrapper s (TPrimType PTBool)   = s ++ "getBool"
        typeWrapper s (TPrimType PTByte)   = "cast[uint8](" ++ s ++ ".getInt)"
        typeWrapper s (TPrimType PTShort)  = "cast[int16](" ++ s ++ ".getInt)"
        typeWrapper s (TPrimType PTUShort) = "cast[uint16](" ++ s ++ ".getInt)"
        typeWrapper s (TPrimType PTInt)    = s ++ ".getInt"
        typeWrapper s (TPrimType PTUInt)   = "cast[uint](" ++ s ++ ".getInt)"
        typeWrapper s (TPrimType PTLong)   = s ++ ".getBiggestInt"
        typeWrapper s (TPrimType PTULong)  = "cast[uint64]](" ++ s ++ ".getBiggestInt)"
        typeWrapper s (TPrimType PTReal)   = s ++ ".getFloat"
        typeWrapper s (TPrimType PTChar)   = "if len(" ++ s ++ ".getStr) > 0: " ++ s ++ ".getStr()[0] else: '\\0'"
        typeWrapper s (TPrimType PTString) = s ++ ".getStr"
        typeWrapper s (TList t)            = s ++ ".getElems.mapIt(" ++ (typeWrapper "it" t) ++ ")"
        typeWrapper s (TDict PTString t)   = s ++ ".getFields.mapIt((it[0], " ++ (typeWrapper "it[1]" t) ++ "))"
        typeWrapper s _                    = s

        generateAttributeFromJson : Nat -> Parameter -> String
        generateAttributeFromJson idt (n, t, _)
          = let lhs = (indent idt) ++ "result." ++ (toNimName n)
                rhs = typeWrapper ("node{" ++ (show n) ++"}") t in
                lhs ++ " = " ++ rhs

        generateModelFromJson : Nat -> List Parameter -> String
        generateModelFromJson idt ps = join "\n" $ map (generateAttributeFromJson idt) ps

    generateMainModule : Fsm -> String
    generateMainModule fsm
      = join "\n\n" [ "when isMainModule:"
                    , generateOutputDelegates indentDelta fsm
                    , generateMainCode indentDelta fsm
                    ]
      where
        generateOutputDelegate : Nat -> SortedMap Expression Tipe -> String -> String -> Action -> String
        generateOutputDelegate idt env pre name (OutputAction n es)
          = let funname = "output_" ++ (toNimName n)
                indexed = enumerate $ map (\x => fromMaybe TUnit $ inferType env x) es in
                join "\n" [ (indent idt) ++ "proc " ++ funname ++ "(" ++ (join ", " (map (\(n', t) => (toNimName n') ++ ": " ++ (toNimType t)) (("model", TRecord (pre ++ "Model") []) :: (map (\(i, t) => ("a" ++ show i, t)) indexed)))) ++ ") ="
                          , (indent (idt + indentDelta)) ++ "queue.addLast(proc (ctx: ServiceContext) ="
                          , (indent (idt + indentDelta * 2)) ++ "info \"" ++ funname ++ " \", ctx.fsmid" ++ (foldl (\acc, (i, t) => acc ++ ", \" \", a" ++ (show i)) "" indexed)
                          , (indent (idt + indentDelta * 2)) ++ name ++ "_" ++ funname ++ "(" ++ (foldl (\acc, (i, _) => acc ++ ", a" ++ (show i)) "ctx, model" indexed) ++ ")"
                          , (indent (idt + indentDelta)) ++ ")"
                          ]
        generateOutputDelegate idt env pre name _ = ""

        generateOutputDelegates : Nat -> Fsm -> String
        generateOutputDelegates idt fsm
          = let env = rootEnv fsm
                name = toNimName fsm.name
                pre = camelize name
                as = outputActions fsm in
                join "\n\n" $ map (generateOutputDelegate idt env pre name) as

        generateMainCode : Nat -> Fsm -> String
        generateMainCode idt fsm
          = let name = toNimName fsm.name
                pre = camelize name
                aas = assignmentActions fsm
                aes = filter applicationExpressionFilter $ flatten $ map expressionsOfAction aas
                oas = outputActions fsm
                ges = nub $ filter applicationExpressionFilter $ flatten $ map expressionsOfTestExpression $ flatten $ map guardsOfTransition fsm.transitions in
                join "\n" [ (indent idt) ++ "let"
                          , generateInitActionDelegate (idt + indentDelta) pre name aes
                          , generateInitOutputDelegate (idt + indentDelta) pre oas
                          , generateInitGuardDelegate (idt + indentDelta) pre name ges
                          , generateInitStateMachine (idt + indentDelta) pre (length aes > Z) (length oas > Z) (length ges > Z)
                          , generateInitServiceDelegate (idt + indentDelta) pre
                          , (indent idt) ++ "run[" ++ pre ++ "StateMachine, " ++ pre ++ "Model](bfsm, \"%%NAME%%\", \"%%DBUSER%%\", \"%%DBNAME%%\", \"%%TABLE-NAME%%\", \"%%INPUT-QUEUE%%\", \"%%OUTPUT-QUEUE%%\", delegate)"
                          ]
          where
            generateInitActionDelegate : Nat -> String -> String -> List Expression -> String
            generateInitActionDelegate idt pre name []  = ""
            generateInitActionDelegate idt pre name aes = join "\n" [ (indent idt) ++ "action_delegate = " ++ pre ++ "ActionDelegate("
                                                                    , join ",\n" $ map (generateInitActionDelegate' (idt + indentDelta) name) aes
                                                                    , (indent idt) ++ ")"
                                                                    ]
              where
                generateInitActionDelegate' : Nat -> String -> Expression -> String
                generateInitActionDelegate' idt name (ApplicationExpression n _) = (indent idt) ++ (toNimName n) ++ ": " ++ name ++ "_action_" ++ (toNimName n)
                generateInitActionDelegate' idt name _                           = ""

            generateInitOutputDelegate : Nat -> String -> List Action -> String
            generateInitOutputDelegate idt pre [] = ""
            generateInitOutputDelegate idt pre as = join "\n" [ (indent idt) ++ "output_delegate = " ++ pre ++ "OutputDelegate("
                                                              , join ",\n" $ map (generateInitOutputDelegate' (idt + indentDelta)) as
                                                              , (indent idt) ++ ")"
                                                              ]
              where
                generateInitOutputDelegate' : Nat -> Action -> String
                generateInitOutputDelegate' idt (OutputAction n _) = (indent idt) ++ (toNimName n) ++ ": output_" ++ (toNimName n)
                generateInitOutputDelegate' idt _ = ""

            generateInitGuardDelegate : Nat -> String -> String -> List Expression -> String
            generateInitGuardDelegate idt pre name [] = ""
            generateInitGuardDelegate idt pre name es = join "\n" [ (indent idt) ++ "guard_delegate = " ++ pre ++ "GuardDelegate("
                                                                  , join ",\n" $ map (generateInitGuardDelegate' (idt + indentDelta) name) es
                                                                  , (indent idt) ++ ")"
                                                                  ]
              where
                generateInitGuardDelegate' : Nat -> String -> Expression -> String
                generateInitGuardDelegate' idt name (ApplicationExpression n _) = (indent idt) ++ (toNimName n) ++ ": " ++ name ++ "_guard_" ++ (toNimName n)
                generateInitGuardDelegate' idt name _ = ""

            generateInitStateMachine : Nat -> String -> Bool -> Bool -> Bool -> String
            generateInitStateMachine idt pre ad od gd
              = let code = [ (indent idt) ++ "bfsm = " ++ pre ++ "StateMachine("
                           , if ad then (indent (idt + indentDelta)) ++ "action_delegate: action_delegate," else ""
                           , if od then (indent (idt + indentDelta)) ++ "output_delegate: output_delegate," else ""
                           , if gd then (indent (idt + indentDelta)) ++ "guard_delegate: guard_delegate," else ""
                           , (indent idt) ++ ")"
                           ] in
                    join "\n" $ filter (\x => length x > Z) code

            generateInitServiceDelegate : Nat -> String -> String
            generateInitServiceDelegate idt pre
              = join "\n" [ (indent idt) ++ "delegate = ServiceDelegate[" ++ pre ++ "StateMachine, " ++ pre ++ "Model]("
                          , (indent (idt + indentDelta)) ++ "play_event: play_event,"
                          , (indent (idt + indentDelta)) ++ "from_json: from_json,"
                          , (indent (idt + indentDelta)) ++ "to_json: to_json,"
                          , (indent idt) ++ ")"
                          ]

loadFsm : String -> Either String Fsm
loadFsm src
  = case parseSExp src of
         Left (Error e _) => Left e
         Right (sexp, _) => case analyse sexp of
                                 Left (Error e _) => Left e
                                 Right (fsm, _) => case check fsm defaultCheckingRules of
                                                        Just errs => Left $ foldl (\a, x => a ++ "\n" ++ x) "" errs
                                                        Nothing => Right fsm

doWork : String -> IO ()
doWork src
  = do
    r <- readFile src
    case r of
         Left e => putStrLn $ show e
         Right c => case loadFsm c of
                         Left e => putStrLn $ e
                         Right fsm => putStrLn $ toNim fsm

usage : IO ()
usage
  = putStrLn "Usage: pfsm-to-nim-service2 <src>"

main : IO ()
main
  = do
    args <- getArgs
    case args of
         x0 :: x1 :: [] => doWork x1
         _ => usage
