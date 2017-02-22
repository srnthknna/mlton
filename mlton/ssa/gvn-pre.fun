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

open Exp Transfer VExp

structure ValTable =
struct
(* Keep a hash table of canonicalized Exps that are in scope. *)
val table: {hash: word, vexp: VExp.t, values: VExp.t list} HashSet.t =
    HashSet.new {hash = #hash}
		
fun lookup (vexp, hash) =
  HashSet.peek
      (table, hash,
       fn {vexp = vexp', ...} => VExp.equals (vexp, vexp'))
      
fun lookupOrAddHelper (value, vexp, hash) =
  HashSet.lookupOrInsert
      (table, hash,
       fn {vexp = vexp', ...} => VExp.equals (vexp, vexp'),
       fn () => {vexp = vexp,
		 hash = hash,
		 values = value})
	
fun lookupOrAdd(vexp, hash) =
  let
      val x = lookup(vexp, hash)
  in
      case x of
	  NONE  => lookupOrAddHelper([], vexp, hash)
	| SOME x => x 
  end
      
fun remove (vexp, hash) =
  HashSet.remove
      (table, hash,
       fn {vexp = vexp', ...} => VExp.equals (vexp, vexp'))
      
fun add (vexp, values, hash) =
  let
      val insertedVal = lookupOrAddHelper(List.concat([values, [vexp]]), vexp, hash)
  in
      ()
  end

fun prettyPrinter holder  = HashSet.foreach (table,
					     fn {hash, vexp, values} =>
						print ("HASH : " ^ (Word.toString hash) ^ " EXP : " ^ "" ^ " VALUES : " ^ "") )
	
end
    
    
structure LabelInfo =
struct
datatype t = T of {dom: Label.t option ref,
                       tmpGen: Var.t list ref,
                       expGen: VExp.t list ref,
		       phiGen: Var.t list ref,
                       availOut: VExp.t list ref,
		       availIn: VExp.t list ref,
		       anticOut: VExp.t list ref,
		       anticIn: VExp.t list ref}
		      
fun new () = T {dom = ref NONE,
                tmpGen = ref [],
                expGen = ref [],
		phiGen = ref [],
                availOut = ref [],
		availIn = ref [],
		anticOut = ref [],
		anticIn = ref []}
	       
	       
	       
(* convenience functions for extracting components *)
local
    fun make f (T r) = f r
    fun make' f = (make f, ! o (make f))
in
    val (dom', dom) = make' #dom
    val (tmpGen', tmpGen) = make' #tmpGen
    val (expGen', expGen) = make' #expGen
    val (phiGen', phiGen) = make' #phiGen
    val (availOut', availOut) = make' #availOut
    val (availIn', availIn) = make' #availIn
    val (anticOut', anticOut) = make' #anticOut
    val (anticIn', anticIn) = make' #anticIn
end
end
    
fun transform (Program.T {globals, datatypes, functions, main}) =
  let		 
      val {get = getLabelInfo, ...} =
	  Property.get
	      (Label.plist, Property.initFun (fn _ => LabelInfo.new ()))
	      
      fun handlePhiCondtions(v, label) =
	let
	    val () = ValTable.add(VExp.VVar v, [], VExp.hash (VExp.VVar v))
	    val () = LabelInfo.phiGen' (getLabelInfo label) := (LabelInfo.phiGen (getLabelInfo label))@[v]
	in
	    ()
	end

      fun doNonFunctional(v, label) =
	let
	    val () = ValTable.add(VVar v, [], VExp.hash (VVar v))
	    val () = LabelInfo.tmpGen' (getLabelInfo label) := (LabelInfo.tmpGen (getLabelInfo label))@[v]
	in
	    ()
	end

      fun handleStatements(s, label) =
	let
	    val Statement.T {var, ty, exp} = s
	    val () =
		(case var of
		     NONE => ()
		   | SOME var' => (case exp  of
				       Var v =>
				       (let
					   val {vexp, hash, values} = case ValTable.lookup(VVar v, VExp.hash (VVar v)) of
									 SOME found => found
					   val () =  ValTable.add(VVar var', values, VExp.hash (VVar var'))
					   val () = LabelInfo.expGen' (getLabelInfo label) := (LabelInfo.expGen (getLabelInfo label))@[VVar v]
					   val () = LabelInfo.tmpGen' (getLabelInfo label) := (LabelInfo.tmpGen (getLabelInfo label))@[var']
				   in
				       ()
				       end)
				     | PrimApp {args, prim, targs} =>
				       (let
					   val isFunctional = Prim.isFunctional prim
				       in
					   if isFunctional
					   then (let
						    val valuesList = Vector.map(args, fn arg =>
										     case ValTable.lookup(VVar arg, VExp.hash (VVar arg)) of
											 SOME found =>
											 let
											     val {hash, vexp, values} = found
											 in
											     values
											 end
									       )
						    val {hash, vexp, values} = case ValTable.lookup(VPrimApp {args=valuesList, prim=prim}, VExp.hash (VPrimApp {args=valuesList, prim=prim})) of
								SOME found => found
						    val () = ValTable.add(VVar var', values, VExp.hash (VVar var'))
						    val addExps = Vector.map(args, fn arg => LabelInfo.expGen' (getLabelInfo label) := (LabelInfo.expGen (getLabelInfo label))@[VVar arg])
						    val () = LabelInfo.expGen' (getLabelInfo label) := (LabelInfo.expGen (getLabelInfo label))@[VPrimApp {args=valuesList, prim=prim}]
						    val () = LabelInfo.tmpGen' (getLabelInfo label) := (LabelInfo.tmpGen (getLabelInfo label))@[var']
						in
						    ()
						end)
					   else doNonFunctional (var', label)
				       end)
				     | _  => doNonFunctional (var', label)
				  ) 
		)
	in
	    case var of
		NONE => ()
	      | SOME var' =>
		let
		    val () = LabelInfo.availOut' (getLabelInfo label) := (LabelInfo.availOut (getLabelInfo label))@[VVar var']
		in
		    ()
		end
	end

      fun handleTransfer t = ()
	    
      fun doBuildSets_Phase1 (block,label) =
	let
	    val Block.T {args,label,statements,transfer} = block
            val doArgs = Vector.map(args, fn (a,b) => handlePhiCondtions(a, label))
	    val doStatements = Vector.map(statements, fn s => handleStatements(s, label))
	    val doTransfer = handleTransfer transfer
	in
	    ()
	end
	    
      fun loopTree (blockTree, parent) =
	let
	    val Tree.T (block, children) = blockTree
	    val label = Block.label block
	    val () = LabelInfo.dom' (getLabelInfo label) := parent
	    val labelInfoObj = (getLabelInfo label)
	    val () = LabelInfo.availOut' labelInfoObj := (case (LabelInfo.dom labelInfoObj) of
							     SOME domLabel => LabelInfo.availOut (getLabelInfo domLabel)
							  |   NONE         => [])
            val () = doBuildSets_Phase1 (block, label)
	    val () = Tree.Seq.foreach (children,fn child => loopTree (child, SOME label))
	in
	    ()
	end

      val globalLabel = Label.fromString "globals"
      val handleGlobal = Vector.map(globals, fn s => handleStatements(s, globalLabel))
	      
      val functions = List.map(functions,fn f =>
				     let
					 val {args, blocks, mayInline, name, raises, returns, start} = Function.dest f
					 val () = loopTree ((Function.dominatorTree f),NONE)
				     in
					 Function.new {args = args,
						       blocks = blocks,
						       mayInline = mayInline,
						       name = name,
						       raises = raises,
						       returns = returns,
						       start = start}
				     end)	       
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
