(* Copyright (C) 2009,2011 Matthew Fluet.
 * Copyright (C) 1999-2006 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor GvnPre (S: SSA_TRANSFORM_STRUCTS): SSA_TRANSFORM = 
struct

open S

open Exp Transfer
structure ENV =
struct
  structure ValTable =
  struct
  (* Keep a hash table of canonicalized Exps that are in scope. *)
  val table: {hash: word, exp: Exp.t, values: Exp.t list} HashSet.t =
      HashSet.new {hash = #hash}
		  
  fun lookup (exp, hash) =
    HashSet.peek
	(table, hash,
	 fn {exp = exp', ...} => Exp.equals (exp,exp'))
	
  fun lookupOrAddHelper (value, exp, hash) =
    HashSet.lookupOrInsert
	(table, hash,
	 fn {exp = exp', ...} => Exp.equals (exp, exp'),
		   fn () => {exp = exp,
			     hash = hash,
			     values = value})
	
  fun lookupOrAdd(exp, hash) =
    let
	val x = lookup(exp, hash)
    in
	case x of
		  NONE  => lookupOrAddHelper([], exp, hash)
		| SOME x => x 
    end
	
  fun remove (exp, hash) =
    HashSet.remove
	(table, hash,
	 fn {exp = exp', ...} => Exp.equals (exp,exp'))

  fun add (exp, hash) =
    let
	val tupleVal = lookup(exp, hash)
    in
	case tupleVal of
	    NONE   => lookupOrAddHelper([exp], exp, hash)
		| SOME {exp, hash, values} =>
		  let
		      val () = remove(exp, hash)
		  in
		      lookupOrAddHelper(List.concat([values, [exp]]), exp, hash)
		  end
	  end
  end
      
  structure BSets =
  struct
  datatype t = T of {EXP_GEN: {hash: word, exp: Exp.t} HashSet.t, 
		     PHI_GEN: {hash: word, exp: Exp.t} HashSet.t,
		     TMP_GEN: {hash: word, exp: Exp.t} HashSet.t,
		     AVAIL_IN: {hash: word, exp: Exp.t} HashSet.t,
		     AVAIL_OUT: {hash: word, exp: Exp.t} HashSet.t,
		     ANTIC_IN: {hash: word, exp: Exp.t} HashSet.t,
		     ANTIC_OUT: {hash: word, exp: Exp.t} HashSet.t}
			
  fun getSetName (setName, T {EXP_GEN,PHI_GEN,TMP_GEN,AVAIL_IN,AVAIL_OUT,ANTIC_IN,ANTIC_OUT}) =
    case setName of
	"EXP_GEN" => EXP_GEN
      | "PHI_GEN" => PHI_GEN
      | "TMP_GEN" => TMP_GEN
      | "AVAIL_IN" => AVAIL_IN
      | "AVAIL_OUT" => AVAIL_OUT
      | "ANTIC_IN" => ANTIC_IN
      | "ANTIC_OUT" => ANTIC_OUT
			   
  fun lookup(bSet, setName, exp, hash) =
    let
	val set = getSetName (setName, bSet)
    in
	HashSet.peek
	    (set, hash,
	     fn {exp = exp', ...} => Exp.equals (exp,exp'))
    end
	
  fun insert (bSet, setName, exp, hash) =
    let
	val set = getSetName (setName, bSet)  
    in
	HashSet.lookupOrInsert
	    (set, hash,
	     fn {exp = exp', ...} => Exp.equals (exp, exp'),
	     fn () => {exp = exp,
		       hash = hash})
    end

  fun replace (bSet, setName, exp, hash) =
    let
	val set = getSetName (setName, bSet)  
    in
	case lookup (bSet, setName, exp, hash) of
	    NONE => insert (bSet, setName, exp, hash)
	  | SOME X =>
	    let
		val () = HashSet.remove
			     (set, hash,
			      fn {exp = exp', ...} => Exp.equals (exp,exp'))
	    in
		insert (bSet, setName, exp, hash)
	    end
    end
  end
      
  structure BTable =
  struct
  val blockTable: {hash: word, block: Block.t, bsets: BSets.t} HashSet.t =
      HashSet.new {hash = #hash}
		  
  fun lookup (block, hash) =  
    HashSet.peek
	(blockTable, hash,
	 fn {block = block', ...} => Block.equals (block,block'))
	
  fun insert (setName, block, exp, hash) =
    let
	val tupleEntry  = lookup (block, hash)
    in
	case tupleEntry of
            SOME {hash, block, bsets} => BSets.insert (bsets, setName, exp, hash)	       
    end
  end
end
    
fun transform (Program.T {globals, datatypes, functions, main}) =
  let
      val program =
         Program.T {datatypes = datatypes,
                    globals = globals,
                    functions = functions,
                    main = main}
      val _ = Program.clearTop program
   in
      program
   end

end
