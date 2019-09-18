module Plugin (plugin) where

import BasicTypes
import GhcPlugins
import SimplCore

plugin :: Plugin
plugin =
    defaultPlugin {installCoreToDos = install}

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = return $ todo ++ todo ++ todo
