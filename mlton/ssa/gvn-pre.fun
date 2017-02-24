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
(*      
fun remove (vexp, hash) =
  HashSet.remove
      (table, hash,
       fn {vexp = vexp', ...} => VExp.equals (vexp, vexp'))
*)      
fun add (vexp, values, hash) =
  let
      val _ = lookupOrAddHelper(List.concat([values, [vexp]]), vexp, hash)
  in
      ()
  end
      
(*
fun prettyPrinter holder  = HashSet.foreach (table,
					     fn {hash, vexp, values} =>
						print ("HASH : " ^ (Word.toString hash) ^ " EXP : " ^ "" ^ " VALUES : " ^ "") )
*)	
end
    
    
structure LabelInfo =
struct
datatype t = T of {dom: Label.t option ref,
                       tmpGen: VExp.t list ref,
                       expGen: VExp.t list ref,
		       phiGen: VExp.t list ref,
                       availOut: VExp.t list ref,
		       availIn: VExp.t list ref,
(*		       anticOut: VExp.t list ref,
*)		       anticIn: VExp.t list ref}
		      
fun new () = T {dom = ref NONE,
                tmpGen = ref [],
                expGen = ref [],
		phiGen = ref [],
                availOut = ref [],
		availIn = ref [],
(*		anticOut = ref [],
*)		anticIn = ref []}
	       
	       
	       
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
    val (availIn', _) = make' #availIn
(*  val (anticOut', anticOut) = make' #anticOut
*)  val (anticIn', anticIn) = make' #anticIn
end
end
    
fun transform (Program.T {globals, datatypes, functions, main}) =
  let		 
      val {get = getLabelInfo, ...} =
	  Property.get
	      (Label.plist, Property.initFun (fn _ => LabelInfo.new ()))
	      
      fun doNonFunctional(v, label) =
	let
	    val () = ValTable.add(VVar v, [], VExp.hash (VVar v))
	    val () = LabelInfo.tmpGen' (getLabelInfo label) := (LabelInfo.tmpGen (getLabelInfo label))@[VVar v]
	in
	    ()
	end

      fun valInsert lst l = if List.contains(lst,l,VExp.equals)
			    then lst
			    else lst@[l]

      fun handlePhiCondtions(v, label) =
	let
	    val () = ValTable.add(VVar v, [], VExp.hash (VVar v))
	    val () = LabelInfo.phiGen' (getLabelInfo label) := (LabelInfo.phiGen (getLabelInfo label))@[VVar v]
	in
	    ()
	end

      fun handleTransfer _ = ()

      fun handleStatements(s, label) =
	let
	    val Statement.T {var=var, exp=exp,...} = s
	    val () =
		(case var of
		     NONE => ()
		   | SOME var' => (case exp  of
				       Var v =>
				       (let
					   val values = case ValTable.lookup(VVar v, VExp.hash (VVar v)) of
							    SOME {values=values,...} => values
							  | NONE => []
					   val () = ValTable.add(VVar var', values, VExp.hash (VVar var'))
					   val () = LabelInfo.expGen' (getLabelInfo label) := valInsert (LabelInfo.expGen (getLabelInfo label)) (VVar v)
					   val () = LabelInfo.tmpGen' (getLabelInfo label) := (LabelInfo.tmpGen (getLabelInfo label))@[VVar var']
				   in
				       ()
				       end)
				     | PrimApp {args=args, prim=prim,...} =>
				       (let
					   val isFunctional = Prim.isFunctional prim
				       in
					   if isFunctional
					   then (let
						    val valuesList = Vector.map(args, fn arg =>
										     case ValTable.lookup(VVar arg, VExp.hash (VVar arg)) of
											 SOME found =>
											 let
											     val {values=values,...} = found
											 in
											     values
											 end
										      | NONE => [] 
									       )
						    val {values=values,...} = ValTable.lookupOrAdd(VPrimApp {args=valuesList, prim=prim}, VExp.hash (VPrimApp {args=valuesList, prim=prim}))  
						    val () = ValTable.add(VVar var', values, VExp.hash (VVar var'))
						    val _ = Vector.map(args, fn arg => LabelInfo.expGen' (getLabelInfo label) := valInsert (LabelInfo.expGen (getLabelInfo label)) (VVar arg))
						    val () = LabelInfo.expGen' (getLabelInfo label) := valInsert (LabelInfo.expGen (getLabelInfo label)) (VPrimApp {args=valuesList, prim=prim})
						    val () = LabelInfo.tmpGen' (getLabelInfo label) := (LabelInfo.tmpGen (getLabelInfo label))@[VVar var']
						in
						    ()
						end)
					   else doNonFunctional (var', label)
				       end)
				     | _  => doNonFunctional (var', label) (* Not sure how to handle other exps*)
				  ) 
		)
	in
	    case var of
		NONE => ()
	      | SOME var' =>
		let
		    val () = LabelInfo.availOut' (getLabelInfo label) := valInsert (LabelInfo.availOut (getLabelInfo label)) (VVar var')
		in
		    ()
		end
	end

	    
      fun doBuildSets_Phase1 (block) =
	let
	    val label = Block.label block
	    val Block.T {args,label,statements,transfer} = block
            val _ = Vector.map(args, fn (a, _) => handlePhiCondtions(a, label)) (*Is this the same args as goto?(they are function args right?) or should I handle them from dom blocks transfers*)
	    val _ = Vector.map(statements, fn s => handleStatements(s, label))
	    val _ = handleTransfer transfer (*Is there any thing to be handled here*)
	in
	    ()
	end

      fun loopTree_Phase1 (blockTree, parent) =
	let
	    val Tree.T (block, children) = blockTree
	    val label = Block.label block
	    val () = LabelInfo.dom' (getLabelInfo label) := parent
	    val labelInfoObj = (getLabelInfo label)
	    val () = LabelInfo.availOut' labelInfoObj := (case (LabelInfo.dom labelInfoObj) of
							     SOME domLabel => LabelInfo.availOut (getLabelInfo domLabel)
							  |   NONE         => [])
            val () = doBuildSets_Phase1 (block)
	    val () = LabelInfo.availIn' labelInfoObj := (case (LabelInfo.dom labelInfoObj) of
							      SOME domLabel => LabelInfo.availOut (getLabelInfo domLabel)
							   |   NONE         => [])
	    val () = Tree.Seq.foreach (children,fn child => loopTree_Phase1 (child, SOME label))
	in
	    ()
	end

	    
      fun diff(lst1, lst2) =
	let
	    val {intersect=intersect,...} = (List.set {equals=VExp.equals, layout=VExp.layout})
	    val intersection = intersect (lst1, lst2)
	    fun difference [] _ = [] 
	      | difference (l::ls) (bs) = if (List.contains(bs, l, VExp.equals))
					  then (difference ls bs)
					  else (l::(difference ls bs)) 
	in
	    (difference lst1 intersection)
	end

      fun clean(lst1) = lst1 (*TODO*)

      fun checkEquals [] [] = true
	| checkEquals (l::ls) (b::bs) = VExp.equals(l,b) andalso (checkEquals ls bs)
	| checkEquals _ _  = false 

      fun findLeader(lst1, lst2) = (*TODO*)
	let
	    val {intersect=intersect,...} = (List.set {equals=VExp.equals, layout=VExp.layout})
	in
	    if  (List.length (intersect (lst1, lst2))>0)
	    then SOME (List.first (intersect (lst1, lst2)))
	    else NONE
	end

      fun evaluateList [] = false
	| evaluateList (l::ls) = l orelse evaluateList ls 
	    
      fun phiTranslate (lst, _, _) = lst (*TODO*)

      fun handleSuccesors (block, childrenCount, children) = if childrenCount=1
					      then phiTranslate (LabelInfo.anticIn (getLabelInfo block), block, children)
					      else if (childrenCount>1)
					      then
						  (
						    let
							val worklist = Vector.toList (children)
							val Tree.T (block, _) = List.first worklist
							val label = Block.label block  
							val ref ANTIC_OUT = LabelInfo.anticIn' (getLabelInfo label)
											  
							fun handleWorkList ANTIC_OUT worklist =
							    (
							      let
								  val Tree.T (block, _) = List.pop worklist
										    
								  val b'label = Block.label block 
								  val () =
								      List.foreach(ANTIC_OUT, fn e => 
												 let 
												     val v = ValTable.lookup(e, VExp.hash e)
												     val {remove=remove,...} = (List.set {equals=VExp.equals, layout=VExp.layout})
												     val valList = case v of
														       SOME {values=values,...} => values
														     | NONE  => [] 
																    (*ambiquity to work with b' or b*)
												     val _ =
													 case findLeader(LabelInfo.anticIn (getLabelInfo b'label), valList)  of 
													     NONE => remove (ANTIC_OUT, e)
													   | SOME _ => ANTIC_OUT  
												 in
												     ()
												 end
										  )
							      in
								  ANTIC_OUT 
							      end
							    )
						    in
							(handleWorkList ANTIC_OUT (ref worklist)) 
						    end
						  ) 
					      else []
      
      fun loopTree_Phase2 (blockTree) =
	let
	    val Tree.T (block, children) = blockTree
	    val label = Block.label block
	    val old = LabelInfo.anticIn (getLabelInfo label)
	    val childrenCount = Tree.Seq.fold(children, 0, fn (_,b) => b+1)
	    val ANTIC_OUT = handleSuccesors (label, childrenCount, children)
	    val S = diff(ANTIC_OUT, LabelInfo.tmpGen (getLabelInfo label))
	    val () = LabelInfo.anticIn' (getLabelInfo label) := diff(LabelInfo.expGen (getLabelInfo label), LabelInfo.tmpGen (getLabelInfo label))
	    val () = List.foreach(S, fn s =>
					let
					    val values = case ValTable.lookup(s, VExp.hash s) of
									  NONE => []
									| SOME {values=values,...} => values 
					    val leader = findLeader(LabelInfo.expGen (getLabelInfo label), values)
					    val () = case leader of
							  NONE => LabelInfo.expGen' (getLabelInfo label) := (LabelInfo.expGen (getLabelInfo label))@[s]
						       |  SOME _ =>  LabelInfo.expGen' (getLabelInfo label) := (LabelInfo.expGen (getLabelInfo label))
					in
					    ()
					end
				 )
	    val () = LabelInfo.anticIn' (getLabelInfo label) := clean(LabelInfo.anticIn (getLabelInfo label))
	    val changed = if (checkEquals old  (LabelInfo.anticIn (getLabelInfo label))) 
			     then false  
			     else true 
	    val changedList = Tree.Seq.map (children,fn child => loopTree_Phase2 (child))
					   
	in
	    evaluateList (changed::(Vector.toList (changedList)))
	end

      fun doBuildSets_Phase2 (blockTree) =
	let
	    val changed = loopTree_Phase2(blockTree)
	    val isChanged = if (changed)
			    then doBuildSets_Phase2(blockTree)
			    else false
	in
	    isChanged 
	end
	    
      val globalLabel = Label.fromString "globals"
      val _ = Vector.map(globals, fn s => handleStatements(s, globalLabel))
	      
      val functions = List.map(functions,fn f =>
				     let
					 val {args, blocks, mayInline, name, raises, returns, start} = Function.dest f
					 val () = loopTree_Phase1 ((Function.dominatorTree f), NONE)
					 val _ = doBuildSets_Phase2((Function.dominatorTree f))
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
