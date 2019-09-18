module Plugin (plugin) where

import BasicTypes
import GhcPlugins
import SimplCore

plugin :: Plugin
plugin =
    defaultPlugin {installCoreToDos = install}

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install (n:_) todo = return $ replicate (read n) todo >>= id
install _ todo = return $ todo ++ todo ++ todo
