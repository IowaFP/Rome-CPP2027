--------------------------------------------------------------------------------
-- Type-check All modules

module Rome.All where 

--------------------------------------------------------------------------------
-- This dir 

open import Rome.Prelude 

--------------------------------------------------------------------------------
-- Kinds   

-- Syntax and GVars
open import Rome.Kinds
open import Rome.Kinds.Properties

--------------------------------------------------------------------------------
-- Types  

open import Rome.Types
open import Rome.Types.Properties 
open import Rome.Types.Properties.Derivable

--------------------------------------------------------------------------------
-- NormalTypes 

open import Rome.NormalTypes

open import Rome.NormalTypes.Properties
open import Rome.NBE

--------------------------------------------------------------------------------
-- Metatheory

open import Rome.Metatheory