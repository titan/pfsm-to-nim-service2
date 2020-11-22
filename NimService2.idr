module NimService2

import Data.Maybe
import Data.List
import Data.List1
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
import Pfsm.Nim

indentDelta : Nat
indentDelta = 2

%hide Data.Vect.(::)

toNim : Fsm -> String
toNim fsm
  = let name = fsm.name
        pre = camelize name
        events = fsm.events
        records = liftRecords fsm.model in
        join "\n\n" $ List.filter nonblank [ generateImports name
                                           , generateTypes
                                           , "var queue = initDeque[MessageFunc](8)"
                                           , generateJsonToRecords records
                                           , generateRecordsToJson records
                                           , generatePlayEvent pre events
                                           , generateToJson pre fsm.model
                                           , generateFromJson pre fsm.model
                                           , generateMainModule pre name fsm
                                           ]
  where
    generateImports : String -> String
    generateImports name
      = let n = toNimName name in
            List.join "\n" [ "import deques, json, logging, service2, sequtils, strtabs, strutils, times"
                           , "import redis except `%`"
                           , "import " ++ n
                           , "import " ++ n ++ "_delegates"
                           ]

    generateTypes : String
    generateTypes
      = List.join "\n" [ "type"
                       , (indent indentDelta) ++ "MessageFunc = proc (ctx: ServiceContext): void"
                       ]

    generateJsonToRecords : List Tipe -> String
    generateJsonToRecords ts
      = join "\n" $ filter nonblank $ map generateJsonToRecord ts
      where
        generateAssignment : Nat -> Parameter -> String
        generateAssignment idt (n, t, _)
          = (indent idt) ++ (toNimName n) ++ " = " ++ (toNimFromJson ("node{\"" ++ n ++ "\"}") t)

        generateJsonToRecord : Tipe -> String
        generateJsonToRecord (TRecord n ps) = List.join "\n" [ "proc jsonTo" ++ (camelize n) ++ "(node: JsonNode): " ++ (camelize n) ++ " ="
                                                             , (indent indentDelta) ++ "let"
                                                             , join "\n" $ map (generateAssignment (indentDelta * 2)) ps
                                                             , (indent indentDelta) ++ "result = " ++ (camelize n) ++ "(" ++ (join ", " (map (\(n, _, _) => (toNimName n) ++ ": " ++ (toNimName n)) ps)) ++ ")"
                                                             ]
        generateJsonToRecord _              = ""

    generateRecordsToJson : List Tipe -> String
    generateRecordsToJson ts
      = join "\n" $ filter nonblank $ map generateRecordToJson ts
      where
        generateToJson : Nat -> Parameter -> String
        generateToJson idt (n, (TPrimType PTLong), _)
          = (indent idt) ++ "result.add(\"" ++ n ++ "\", % $data." ++ (toNimName n) ++ ")"
        generateToJson idt (n, (TPrimType PTULong), _)
          = (indent idt) ++ "result.add(\"" ++ n ++ "\", % $data." ++ (toNimName n) ++ ")"
        generateToJson idt (n, (TList (TPrimType PTLong)), _)
          = (indent idt) ++ "result.add(\"" ++ n ++ "\", %data." ++ (toNimName n) ++ ".mapIt($it))"
        generateToJson idt (n, (TList (TPrimType PTULong)), _)
          = (indent idt) ++ "result.add(\"" ++ n ++ "\", %data." ++ (toNimName n) ++ ".mapIt($it))"
        generateToJson idt (n, _, _)
          = (indent idt) ++ "result.add(\"" ++ n ++ "\", %data." ++ (toNimName n) ++ ")"

        generateRecordToJson : Tipe -> String
        generateRecordToJson (TRecord n ps)
          = List.join "\n" [ "proc " ++ (camelize n) ++ "ToJson(data: " ++ (camelize n) ++ "): JsonNode ="
                           , (indent indentDelta) ++ "result = newJObject()"
                           , join "\n" $ map (generateToJson indentDelta) ps
                           ]
        generateRecordToJson _
          = ""

    generatePlayEvent : String -> List1 Event -> String
    generatePlayEvent pre es
      = List.join "\n" [ "proc play_event(fsm: " ++ pre ++ "StateMachine, model: " ++ pre ++ "Model, context: ServiceContext, event: string, payload: JsonNode): " ++ pre ++ "Model ="
                       , (indent indentDelta) ++ "case event:"
                       , generateEventHandlers (indentDelta * 2) es
                       , (indent (indentDelta * 2)) ++ "else:"
                       , generateDefaultEventHandler (indentDelta * 3)
                       ]
      where
        generateEventHandle : Nat -> Event -> String
        generateEventHandle idt evt@(MkEvent n ps _)
          = let srcs = [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                       , generateFetchEventArgs (idt + indentDelta) ps
                       , generateEventCall (idt + indentDelta) evt
                       , generateQueueHandler (idt + indentDelta)
                       ] in
                join "\n" $ List.filter (\x => length x > 0) srcs
          where
            generateFetchEventArg : Nat -> Parameter -> String
            generateFetchEventArg idt (n, t, _)
              = let lhs = (indent idt) ++ (toNimName n)
                    rhs = "payload{\"" ++ n ++ "\"}" in
                    lhs ++ " = " ++ (toNimFromJson rhs t)

            generateFetchEventArgs : Nat -> List Parameter -> String
            generateFetchEventArgs idt ps
              = let args = map (generateFetchEventArg (idt + indentDelta)) ps in
                    if length args > 0
                       then (indent idt) ++ "let\n" ++ (join "\n" args)
                       else ""

            generateEventCall : Nat -> Event -> String
            generateEventCall idt (MkEvent n ps _)
              = (indent idt) ++ "result = " ++ (toNimName n) ++ "(" ++ (List.join ", " (map (\(n, _, _) => toNimName n) (("fsm", (TPrimType PTBool), Nothing) :: (("model", (TPrimType PTBool), Nothing) :: ps)))) ++ ")"

            generateQueueHandler : Nat -> String
            generateQueueHandler idt
              = List.join "\n" [ (indent idt) ++ "while len(queue) > 0:"
                               , (indent (idt + indentDelta)) ++ "let msgfun = queue.popFirst"
                               , (indent (idt + indentDelta)) ++ "msgfun(context)"
                               ]

        generateEventHandlers : Nat -> List1 Event -> String
        generateEventHandlers idt es
          = List1.join "\n" $ map (generateEventHandle idt) es

        generateDefaultEventHandler : Nat -> String
        generateDefaultEventHandler idt
          = List.join "\n" [ (indent idt) ++ "info \"Unknown event: \" & event"
                           , (indent idt) ++ "info pretty(payload)"
                           , (indent idt) ++ "result = model"
                           ]

    generateToJson : String -> List Parameter -> String
    generateToJson pre ps
      = List.join "\n" [ "proc to_json(model: " ++ pre ++ "Model): JsonNode ="
                       , (indent indentDelta) ++ "result = newJObject()"
                       , join "\n" $ map (generateModelToJson indentDelta) ps
                       ]
      where
        generateModelToJson : Nat -> Parameter -> String
        generateModelToJson idt (n, (TRecord rn _), _)
          = (indent idt) ++ "result.add(" ++ (show n) ++ ", " ++ (camelize rn) ++ "toJson(model." ++ (toNimName n) ++ "))"
        generateModelToJson idt (n, (TList (TRecord rn _)), _)
          = List.join "\n" [ (indent idt) ++ "let " ++ (toNimName n) ++ " = newJArray()"
                           , (indent idt) ++ "for i in model." ++ (toNimName n) ++ ".mapIt(" ++ (camelize rn) ++ "ToJson(it)):"
                           , (indent (idt + indentDelta)) ++ (toNimName n) ++ ".add(i)"
                           , (indent idt) ++ "result.add(" ++ (show n) ++ ", " ++ (toNimName n) ++ ")"
                           ]
        generateModelToJson idt (n, _, _)
          = (indent idt) ++ "result.add(" ++ (show n) ++ ", % model." ++ (toNimName n) ++ ")"

    generateFromJson : String -> List Parameter -> String
    generateFromJson pre ps
      = List.join "\n" [ "proc from_json(node: JsonNode): " ++ pre ++ "Model ="
                       , (indent indentDelta) ++ "result = new(" ++ pre ++ "Model)"
                       , generateModelFromJson indentDelta ps
                       ]
      where
        generateAttributeFromJson : Nat -> Parameter -> String
        generateAttributeFromJson idt (n, t, _)
          = let lhs = (indent idt) ++ "result." ++ (toNimName n)
                rhs = toNimFromJson ("node{" ++ (show n) ++"}") t in
                lhs ++ " = " ++ rhs

        generateModelFromJson : Nat -> List Parameter -> String
        generateModelFromJson idt ps = join "\n" $ map (generateAttributeFromJson idt) ps

    generateMainModule : String -> String -> Fsm -> String
    generateMainModule pre name fsm
      = let env = rootEnv fsm
            model = fsm.model
            actions = outputActions fsm in
            join "\n\n" $ List.filter nonblank [ "when isMainModule:"
                                               , generateNonDefaultOutputDelegates indentDelta pre name env model actions
                                               , generateDefaultOutputDelegates indentDelta pre name env model actions
                                               , generateMainCode indentDelta pre name env fsm
                                               ]
      where
        generateOutputDelegate : Nat -> String -> String -> SortedMap Expression Tipe -> List Parameter -> (Nat -> String -> String -> List (Nat, Tipe) -> List Parameter -> String) -> Action -> String
        generateOutputDelegate idt pre name env model body (OutputAction n es)
          = let funname = "output_" ++ (toNimName n)
                indexed = enumerate $ map (\x => fromMaybe TUnit $ inferType env x) es in
                List.join "\n" [ (indent idt) ++ "proc " ++ funname ++ "(" ++ (List.join ", " (map (\(n', t) => (toNimName n') ++ ": " ++ (toNimType t)) (("model", TRecord (pre ++ "Model") []) :: (map (\(i, t) => ("a" ++ show i, t)) indexed)))) ++ ") ="
                               , (indent (idt + indentDelta)) ++ "queue.addLast(proc (ctx: ServiceContext) ="
                               , (indent (idt + indentDelta * 2)) ++ "info \"" ++ funname ++ " \", ctx.fsmid" ++ (foldl (\acc, (i, t) => acc ++ (case t of (TPrimType PTString) => ", \" \", a"; _ => ", \" \", $a") ++ (show i)) "" indexed)
                               , body (idt + indentDelta * 2) name funname indexed model
                               , (indent (idt + indentDelta)) ++ ")"
                               ]
        generateOutputDelegate idt env pre name model body _ = ""

        generateNonDefaultOutputDelegates : Nat -> String -> String -> SortedMap Expression Tipe -> List Parameter -> List Action -> String
        generateNonDefaultOutputDelegates idt pre name env model as
          = join "\n\n" $ filter nonblank $ map (generateOutputDelegate idt pre name env model bodyGenerator) $ filter nonDefaultOutputActionFilter as
          where
            nonDefaultOutputActionFilter : Action -> Bool
            nonDefaultOutputActionFilter (OutputAction "add-to-state-list" _)                     = False
            nonDefaultOutputActionFilter (OutputAction "remove-from-state-list" _)                = False
            nonDefaultOutputActionFilter (OutputAction "add-to-state-list-of-participant" _)      = False
            nonDefaultOutputActionFilter (OutputAction "remove-from-state-list-of-participant" _) = False
            nonDefaultOutputActionFilter (OutputAction "response" _)                              = False
            nonDefaultOutputActionFilter (OutputAction "response-id" _)                           = False
            nonDefaultOutputActionFilter (OutputAction "sync-model" _)                            = False
            nonDefaultOutputActionFilter _                                                        = True

            bodyGenerator : Nat -> String -> String -> List (Nat, Tipe) -> List Parameter -> String
            bodyGenerator idt name funname indexed model
              = (indent idt) ++ (toNimName name) ++ "_" ++ funname ++ "(" ++ (foldl (\acc, (i, _) => acc ++ ", a" ++ (show i)) "ctx, model" indexed) ++ ")"

        generateDefaultOutputDelegates : Nat -> String -> String -> SortedMap Expression Tipe -> List Parameter -> List Action -> String
        generateDefaultOutputDelegates idt pre name env model as
          = join "\n\n" $ filter nonblank $ map (generateDefaultOutputDelegate idt pre name env model) $ filter defaultOutputActionFilter as
          where
            defaultOutputActionFilter : Action -> Bool
            defaultOutputActionFilter (OutputAction "add-to-state-list" _)                     = True
            defaultOutputActionFilter (OutputAction "remove-from-state-list" _)                = True
            defaultOutputActionFilter (OutputAction "add-to-state-list-of-participant" _)      = True
            defaultOutputActionFilter (OutputAction "remove-from-state-list-of-participant" _) = True
            defaultOutputActionFilter (OutputAction "response" _)                              = True
            defaultOutputActionFilter (OutputAction "response-id" _)                           = True
            defaultOutputActionFilter (OutputAction "sync-model" _)                            = True
            defaultOutputActionFilter _                                                        = False

            manyToOneFieldFilter : Parameter -> Bool
            manyToOneFieldFilter (_, _, ms) = case lookup "reference" ms of
                                                   Just (MVString _) => case lookup "mapping" ms of
                                                                             Just (MVString "many-to-one") => True
                                                                             _ => False
                                                   _ => False

            generateCacheKeyOfStateList : Nat -> Nat -> String -> String -> String
            generateCacheKeyOfStateList idt idx name ref
              = (indent idt) ++ "key" ++ (show (idx + 1)) ++ " = \"tenant:\" & $ctx.tenant & \"#" ++ ref ++ ":\" & $model." ++ (toNimName ref) ++ " & \"#" ++ name ++ ".\" & a0"

            generateCacheAction : Nat -> Nat -> (Nat -> Nat -> String) -> String
            generateCacheAction idt cnt action
              = generateCacheAction' [] idt cnt action
              where
                generateCacheAction' : List String -> Nat -> Nat -> (Nat -> Nat -> String) -> String
                generateCacheAction' acc idt Z     action = List.join "\n" ((action idt 0) :: acc)
                generateCacheAction' acc idt (S n) action = generateCacheAction' ((action idt (S n)) :: acc) idt n action

            addToStateListBodyGenerator : Nat -> String -> String -> List (Nat, Tipe) -> List Parameter -> String
            addToStateListBodyGenerator idt name funname indexed model
              = let manyToOneFields = filter manyToOneFieldFilter model in
                    join "\n" $ List.filter nonblank [ (indent idt) ++ "let"
                                                     , (indent (idt + indentDelta)) ++ "occurred_at = cast[int](from_mytimestamp(ctx.occurred_at).toTime.toUnix)"
                                                     , (indent (idt + indentDelta)) ++ "key0 = \"tenant:\" & $ctx.tenant & \"#" ++ name ++ ".\" & a0"
                                                     , List.join "\n" $ map (\(idx, (n, _, _)) => generateCacheKeyOfStateList (idt + indentDelta) idx name n) $ enumerate manyToOneFields
                                                     , if length manyToOneFields > 0 then ((indent idt) ++ "discard ctx.cache_redis.multi") else ""
                                                     , generateCacheAction idt (length manyToOneFields) generateCacheZAddAction
                                                     , if length manyToOneFields > 0 then ((indent idt) ++ "discard ctx.cache_redis.exec") else ""
                                                     ]
              where
                generateCacheZAddAction : Nat -> Nat -> String
                generateCacheZAddAction idt idx
                  = (indent idt) ++ "discard ctx.cache_redis.zadd(key" ++ (show idx) ++ ", @[(occurred_at, $ctx.fsmid)])"

            removeFromStateListBodyGenerator : Nat -> String -> String -> List (Nat, Tipe) -> List Parameter -> String
            removeFromStateListBodyGenerator idt name funname indexed model
              = let manyToOneFields = filter manyToOneFieldFilter model in
                    join "\n" $ List.filter nonblank [ (indent idt) ++ "let"
                                                     , (indent (idt + indentDelta)) ++ "key0 = \"tenant:\" & $ctx.tenant & \"#" ++ name ++ ".\" & a0"
                                                     , List.join "\n" $ map (\(idx, (n, _, _)) => generateCacheKeyOfStateList (idt + indentDelta) idx name n) $ enumerate manyToOneFields
                                                     , if length manyToOneFields > 0 then ((indent idt) ++ "discard ctx.cache_redis.multi") else ""
                                                     , generateCacheAction idt (length manyToOneFields) generateCacheZRemAction
                                                     , if length manyToOneFields > 0 then ((indent idt) ++ "discard ctx.cache_redis.exec") else ""
                                                     ]
              where
                generateCacheZRemAction : Nat -> Nat -> String
                generateCacheZRemAction idt idx
                  = (indent idt) ++ "discard ctx.cache_redis.zrem(key" ++ (show idx) ++ ", @[$ctx.fsmid])"

            addToStateListOfParticipantBodyGenerator : Nat -> String -> String -> List (Nat, Tipe) -> List Parameter -> String
            addToStateListOfParticipantBodyGenerator idt name funname indexed _
              = List.join "\n" [ (indent idt) ++ "let key = \"tenant:\" & $ctx.tenant & \"#\" & a1 & \":\" & $ctx.trigger & \"#" ++ name ++ ".\" & a0"
                               , (indent idt) ++ "discard ctx.cache_redis.zadd(key, @[(cast[int](from_mytimestamp(ctx.occurred_at).toTime.toUnix), $ctx.fsmid)])"
                               ]

            removeFromStateListOfParticipantBodyGenerator : Nat -> String -> String -> List (Nat, Tipe) -> List Parameter -> String
            removeFromStateListOfParticipantBodyGenerator idt name funname indexed _
              = List.join "\n" [ (indent idt) ++ "let key = \"tenant:\" & $ctx.tenant & \"#\" & a1 & \":\" & $ctx.trigger & \"#" ++ name ++ ".\" & a0"
                               , (indent idt) ++ "discard ctx.cache_redis.zrem(key, @[$ctx.fsmid])"
                               ]

            responseBodyGenerator : Nat -> String -> String -> List (Nat, Tipe) -> List Parameter -> String
            responseBodyGenerator idt name funname indexed _
              = List.join "\n" [ (indent idt) ++ "let key = \"tenant:\" & $ctx.tenant & \"#callback:\" & ctx.callback"
                               , (indent idt) ++ "discard ctx.cache_redis.setex(key, \"\"\"{\"code\":$1,\"payload\":\"$2\"}\"\"\" % [$a0, a1], 60)"
                               ]

            responseIdBodyGenerator : Nat -> String -> String -> List (Nat, Tipe) -> List Parameter -> String
            responseIdBodyGenerator idt name funname indexed _
              = List.join "\n" [ (indent idt) ++ "let key = \"tenant:\" & $ctx.tenant & \"#callback:\" & ctx.callback"
                               , (indent idt) ++ "discard ctx.cache_redis.setex(key, \"\"\"{\"code\":200,\"payload\":\"$1\"}\"\"\" % $ ctx.fsmid, 60)"
                               ]

            syncModelBodyGenerator : Nat -> String -> String -> List (Nat, Tipe) -> List Parameter -> String
            syncModelBodyGenerator idt name funname indexed model
              = List.join "\n" [ (indent idt) ++ "let"
                               , (indent (idt + indentDelta)) ++ "key = \"tenant:\" & $ctx.tenant & \"#" ++ name ++ ":\" & $ ctx.fsmid"
                               , (indent (idt + indentDelta)) ++ "args = @{"
                               , generateArguments (idt + indentDelta * 2) model
                               , (indent (idt + indentDelta)) ++ "}"
                               , (indent idt) ++ "discard ctx.cache_redis.hmset(key, args)"
                               ]
              where
                generateArgument : Nat -> Parameter -> String
                generateArgument idt (n, t, _)
                  = (indent idt) ++ "\"" ++ (toUpper n) ++ "\": " ++ (toNimString ("model." ++ (toNimName n)) t)

                generateArguments : Nat -> List Parameter -> String
                generateArguments idt ps
                  = join ",\n" $ map (generateArgument idt) ps

            generateDefaultOutputDelegate : Nat -> String -> String -> SortedMap Expression Tipe -> List Parameter -> Action -> String
            generateDefaultOutputDelegate idt pre name env model act@(OutputAction "add-to-state-list" _)                     = generateOutputDelegate idt pre name env model addToStateListBodyGenerator act
            generateDefaultOutputDelegate idt pre name env model act@(OutputAction "remove-from-state-list" _)                = generateOutputDelegate idt pre name env model removeFromStateListBodyGenerator act
            generateDefaultOutputDelegate idt pre name env model act@(OutputAction "add-to-state-list-of-participant" _)      = generateOutputDelegate idt pre name env model addToStateListOfParticipantBodyGenerator act
            generateDefaultOutputDelegate idt pre name env model act@(OutputAction "remove-from-state-list-of-participant" _) = generateOutputDelegate idt pre name env model removeFromStateListOfParticipantBodyGenerator act
            generateDefaultOutputDelegate idt pre name env model act@(OutputAction "response" _)                              = generateOutputDelegate idt pre name env model responseBodyGenerator act
            generateDefaultOutputDelegate idt pre name env model act@(OutputAction "response-id" _)                           = generateOutputDelegate idt pre name env model responseIdBodyGenerator act
            generateDefaultOutputDelegate idt pre name env model act@(OutputAction "sync-model" _)                            = generateOutputDelegate idt pre name env model syncModelBodyGenerator act
            generateDefaultOutputDelegate idt pre name env model _                                                            = ""


        generateMainCode : Nat -> String -> String -> SortedMap Expression Tipe -> Fsm -> String
        generateMainCode idt pre name env fsm
          = let aas = assignmentActions fsm
                aes = nubBy (applicationExpressionEqualityChecker env) $ filter applicationExpressionFilter $ flatten $ map expressionsOfAction aas
                oas = outputActions fsm
                ges = nubBy (applicationExpressionEqualityChecker env) $ filter applicationExpressionFilter $ flatten $ map expressionsOfTestExpression $ flatten $ List1.toList $ map guardsOfTransition fsm.transitions in
                List.join "\n" $ List.filter nonblank [ (indent idt) ++ "let"
                                                      , generateInitActionDelegates (idt + indentDelta) pre name aes
                                                      , generateInitOutputDelegates (idt + indentDelta) pre oas
                                                      , generateInitGuardDelegates (idt + indentDelta) pre name ges
                                                      , generateInitStateMachine (idt + indentDelta) pre (length aes > Z) (length oas > Z) (length ges > Z)
                                                      , generateInitServiceDelegate (idt + indentDelta) pre
                                                      , (indent idt) ++ "run[" ++ pre ++ "StateMachine, " ++ pre ++ "Model](bfsm, \"%%NAME%%\", \"%%DBUSER%%\", \"%%DBNAME%%\", \"%%TABLE-NAME%%\", \"%%INPUT-QUEUE%%\", \"%%OUTPUT-QUEUE%%\", delegate)"
                                                      ]
          where

            generateInitActionDelegates : Nat -> String -> String -> List Expression -> String
            generateInitActionDelegates idt pre name []  = ""
            generateInitActionDelegates idt pre name aes = List.join "\n" [ (indent idt) ++ "action_delegate = " ++ pre ++ "ActionDelegate("
                                                                          , join ",\n" $ map (generateInitActionDelegate (idt + indentDelta) name) aes
                                                                          , (indent idt) ++ ")"
                                                                          ]
              where
                toActionFuncName : Name -> String
                toActionFuncName "+" = "plus"
                toActionFuncName "-" = "minus"
                toActionFuncName "*" = "multiplay"
                toActionFuncName "/" = "divide"
                toActionFuncName n   = toNimName n

                generateInitActionDelegate : Nat -> String -> Expression -> String
                generateInitActionDelegate idt name (ApplicationExpression n _) = (indent idt) ++ (toNimFuncName n) ++ ": " ++ (toNimName name) ++ "_action_" ++ (toActionFuncName n)
                generateInitActionDelegate idt name _                           = ""

            generateInitOutputDelegates : Nat -> String -> List Action -> String
            generateInitOutputDelegates idt pre [] = ""
            generateInitOutputDelegates idt pre as = List.join "\n" [ (indent idt) ++ "output_delegate = " ++ pre ++ "OutputDelegate("
                                                                    , join ",\n" $ map (generateInitOutputDelegate (idt + indentDelta)) as
                                                                    , (indent idt) ++ ")"
                                                                    ]
              where
                generateInitOutputDelegate : Nat -> Action -> String
                generateInitOutputDelegate idt (OutputAction n _) = (indent idt) ++ (toNimName n) ++ ": output_" ++ (toNimName n)
                generateInitOutputDelegate idt _ = ""

            generateInitGuardDelegates : Nat -> String -> String -> List Expression -> String
            generateInitGuardDelegates idt pre name [] = ""
            generateInitGuardDelegates idt pre name es = List.join "\n" [ (indent idt) ++ "guard_delegate = " ++ pre ++ "GuardDelegate("
                                                                        , join ",\n" $ map (generateInitGuardDelegate (idt + indentDelta) name) es
                                                                        , (indent idt) ++ ")"
                                                                        ]
              where
                generateInitGuardDelegate : Nat -> String -> Expression -> String
                generateInitGuardDelegate idt name (ApplicationExpression n _) = (indent idt) ++ (toNimName n) ++ ": " ++ name ++ "_guard_" ++ (toNimName n)
                generateInitGuardDelegate idt name _ = ""

            generateInitStateMachine : Nat -> String -> Bool -> Bool -> Bool -> String
            generateInitStateMachine idt pre ad od gd
              = let code = [ (indent idt) ++ "bfsm = " ++ pre ++ "StateMachine("
                           , if ad then (indent (idt + indentDelta)) ++ "action_delegate: action_delegate," else ""
                           , if od then (indent (idt + indentDelta)) ++ "output_delegate: output_delegate," else ""
                           , if gd then (indent (idt + indentDelta)) ++ "guard_delegate: guard_delegate," else ""
                           , (indent idt) ++ ")"
                           ] in
                    List.join "\n" $ List.filter (\x => length x > Z) code

            generateInitServiceDelegate : Nat -> String -> String
            generateInitServiceDelegate idt pre
              = List.join "\n" [ (indent idt) ++ "delegate = ServiceDelegate[" ++ pre ++ "StateMachine, " ++ pre ++ "Model]("
                               , (indent (idt + indentDelta)) ++ "play_event: play_event,"
                               , (indent (idt + indentDelta)) ++ "from_json: from_json,"
                               , (indent (idt + indentDelta)) ++ "to_json: to_json,"
                               , (indent idt) ++ ")"
                               ]

doWork : String -> IO ()
doWork src
  = do Right fsm <- loadFsmFromFile src
       | Left err => putStrLn $ show err
       putStrLn $ toNim fsm

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
