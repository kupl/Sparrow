(***********************************************************************)
(*                                                                     *)
(* Copyright (c) 2007-present.                                         *)
(* Programming Research Laboratory (ROPAS), Seoul National University. *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* This software is distributed under the term of the BSD license.     *)
(* See the LICENSE file for details.                                   *)
(*                                                                     *)
(***********************************************************************)
type feature
val select : Global.t -> BasicDom.PowLoc.t -> BasicDom.PowLoc.t 
val extract_feature : Global.t -> BasicDom.PowLoc.t -> feature
