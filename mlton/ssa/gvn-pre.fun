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


val nextValNum =
    let
	val ctr = ref 0
    in
	fn () => (ctr := !ctr + 1 ; !ctr)
    end
	 
structure VExp = (*add the comment inclusions in sig as well*)
   struct

   datatype t = (*Not included other types of values*)
            VConst of Const.t
	    | VPrimApp of {prim: Type.t Prim.t,
			   args: value vector,
                           targs: Type.t vector}
	    | VVar of Var.t
   and value = Value of {vexps: t list ref, id: int}

   fun newValue () = Value {vexps=(ref []), id = nextValNum ()}
			    
   fun valueListEquals (xs, xs') = Vector.equals (xs, xs', valueEquals)
   and valueEquals(xs: value, xs': value) =
       let
           val Value {id=id,...} = xs
           val Value {id=id',...} = xs'
       in
           id=id'
       end
   and equals (e: t, e': t): bool =
       case (e, e') of
           (VConst c, VConst c') => Const.equals (c, c')
         | (VPrimApp {prim, args, ...},
            VPrimApp {prim = prim', args = args',...}) =>
	   Prim.equals (prim, prim') andalso valueListEquals (args, args')	   
         | (VVar x, VVar x') => Var.equals (x, x')
         | _ => false

   fun layoutValue v = case v of
			   Value {id=id,...} => Layout.str (Int.toString id)
	 
   fun layout e =
     let
	 open Layout
	 fun layoutTuple xs = Vector.layout layoutValue xs
     in
	 case e of
	     VConst c => Const.layout c
           | VPrimApp {prim=prim,targs=targs,args=args} =>
             seq [Prim.layout prim,
                  if !Control.showTypes
                  then if 0 = Vector.length targs
                       then empty
                       else Vector.layout Type.layout targs
                  else empty,
                  seq [str " ", layoutTuple args]]
	   | VVar x => Var.layout x
     end
     	 
   local
       val newHash = Random.word
       val primApp = newHash ()

       fun hasher v = 
	 let
	     val Value {id=id,...} = v
	 in
	     Word.fromInt id
	 end
			     
       fun hashValueList (xs: value vector, w: Word.t): Word.t =
	 Vector.fold (xs, w, fn (x, w) => Word.xorb (w, hashValue (x,w)))
       and hashValue (xs: value, w: Word.t): Word.t =
           Word.xorb (w, hasher xs)
   in         
   val hash  = 
    fn (VConst c) => Const.hash c
     | (VPrimApp {args, ...}) => hashValueList (args, primApp) 
     | (VVar x) => Var.hash x
   end
   
   val hash = hash

   end
       
open Exp Transfer VExp
	 
fun toPrettyValue value = case value of
			      Value {vexps=vexps, id=id} => Layout.toString (layoutValue value)
fun toPretty vexp = case vexp of
			(VConst c) => Const.toString c
		      | (VPrimApp {args,prim, ...}) =>
			Layout.toString
			       (Prim.layoutApp (prim, args, fn x =>
							       VExp.layoutValue x)) 
		      | (VVar x) => Var.toString x	 

structure ValTable =
struct
(* Keep a hash table of canonicalized Exps that are in scope. *)
val table: {hash: word, vexp: VExp.t, values: VExp.value } HashSet.t =
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
		 values = (Value {vexps = (ref value), id = 0})})
	
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
end

fun prettyPrinter ()  = HashSet.foreach (ValTable.table,
					     fn {hash, vexp, values} =>
						let 
						    val () = print ("HASH : " ^ (Word.toString hash) ^ " VEXP : " ^ (toPretty vexp) ^  " VALUE : " ^ (toPrettyValue values) )
						in
						    ()
						end)
					    
    
structure LabelInfo =
struct
datatype t = T of {dom: Label.t option ref,
                       tmpGen: Var.t list ref,
                       expGen: VExp.t list ref,
		       phiGen: Var.t list ref,
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
(*		anticOut = ref[],
 *)		anticIn = ref []
	       }
	       
	       
	       
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
	    val () = LabelInfo.tmpGen' (getLabelInfo label) := (LabelInfo.tmpGen (getLabelInfo label))@[v]
	in
	    ()
	end

      fun valInsert vs vexp =
	    if List.contains(!vs, vexp, fn (vexp,vexp') =>
					   let
					       val v = ValTable.lookup(vexp, VExp.hash vexp)
					       val v' = ValTable.lookup(vexp', VExp.hash vexp')
					   in
					       case (v,v') of
						   (SOME {values=value,...},SOME {values=value',...}) => VExp.valueEquals(value,value')
						 | (_,_) => false
					   end
			    )
	    then ()
	    else vs := (!vs)@[vexp]
		 
      fun valReplace lst l = if List.contains(!lst, l, VExp.equals)
			     then
				 let
				     val {remove=remove,...} = (List.set {equals=VExp.equals, layout=VExp.layout})
				     val () = lst := (remove (!lst, l))
				     val () = lst := (!lst)@[l]
				 in
				     ()
				 end
			     else ()
						   
      fun handlePhiCondtions(v, label) =
	let
	    val () = ValTable.add(VVar v, [], VExp.hash (VVar v))
	    val () = LabelInfo.phiGen' (getLabelInfo label) := (LabelInfo.phiGen (getLabelInfo label))@[v]
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
					   val (vexps, value) = case ValTable.lookup(VVar v, VExp.hash (VVar v)) of
							    SOME {values=value,...} => (case value of
											    Value {vexps=vexps,...} => (vexps,value))
							  | NONE => (ref [], VExp.newValue ())
					   val () = ValTable.add(VVar var', !vexps, VExp.hash (VVar var'))
					   val () = (valInsert (LabelInfo.expGen' (getLabelInfo label)) (VVar v))
					   val () = LabelInfo.tmpGen' (getLabelInfo label) := (LabelInfo.tmpGen (getLabelInfo label))@[var']
				   in
				       ()
				       end)
				     | PrimApp {args=args, prim=prim,targs=targs} =>
				       (let
					   val isFunctional = Prim.isFunctional prim
				       in
					   if isFunctional
					   then (let
						    val valueList = Vector.map(args, fn arg =>
										     case ValTable.lookup(VVar arg, VExp.hash (VVar arg)) of
											 SOME {values=value,...} => value
										      | NONE => VExp.newValue ()
									      )
						    val exp = VPrimApp {args=valueList, prim=prim, targs=targs}
						    val {values=primValue,...} = ValTable.lookupOrAdd(exp, VExp.hash exp)
						    val (Value {vexps=values,...}) = primValue
						    val () = ValTable.add(VVar var', !values, VExp.hash (VVar var'))
						    val _ = Vector.map(args, fn arg => (valInsert (LabelInfo.expGen' (getLabelInfo label)) (VVar arg) ))
						    val () = (valInsert (LabelInfo.expGen' (getLabelInfo label)) (VPrimApp {args=valueList, prim=prim, targs=targs}))
						    val () = LabelInfo.tmpGen' (getLabelInfo label) := (LabelInfo.tmpGen (getLabelInfo label))@[var']
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
	      | SOME var' => (valInsert (LabelInfo.availOut' (getLabelInfo label)) (VVar var'))
	end

	    
      fun doBuildSets_Phase1 (block) =
	let
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
(*
      fun diff(values, vars) =
	let
	    fun removeIfPresent [] _ = []
	      | removeIfPresent (v::vs) var = case v of
						  (Value {vexps=vexps,...})=>(if List.contains(!vexps, var, VExp.equals)
									      then vs
									      else (v::(removeIfPresent vs var)))
	    fun removeVars values [] = values 
	      | removeVars values (v::vr) = removeVars (removeIfPresent values v) vr  
	in
	    removeVars values vars
	end
*)
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

      fun findLeader(_, _) = NONE(*TODO*)
(*	let
	    val {intersect=intersect,...} = (List.set {equals=VExp.valueEquals, layout=VExp.layoutValue})
	in
	    if  (List.length (intersect (lst1, lst2))>0)
	    then SOME (List.first (intersect (lst1, lst2)))
	    else NONE
	end
*)
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
							val ANTIC_OUT = ref []
							val () = ANTIC_OUT := LabelInfo.anticIn (getLabelInfo label)
											  
							fun handleWorkList ANTIC_OUT worklist =
							    (
							      let
								  val Tree.T (block, _) = List.pop worklist
										    
								  val b'label = Block.label block 
								  val () =
								      List.foreach(!ANTIC_OUT, fn e => 
												  let
												      val v = ValTable.lookup(e, VExp.hash e)
												      val {remove=remove,...} = (List.set {equals=VExp.equals, layout=VExp.layout})
												      val valList = case v of
															SOME {values=values,...} => values
														     | NONE  => VExp.newValue ()
												      (*ambiquity to work with b' or b*)
												      val () =
													  case findLeader (LabelInfo.anticIn (getLabelInfo b'label), valList)  of 
													      NONE => ANTIC_OUT := (remove (!ANTIC_OUT, e))
													    | SOME _ => ()  
												  in
												      ()
												  end
										  )
							      in
								  !ANTIC_OUT 
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
	    val old = (LabelInfo.anticIn (getLabelInfo label))
	    val childrenCount = Tree.Seq.fold(children, 0, fn (_,b) => b+1)
	    val ANTIC_OUT = ref []
	    val () = ANTIC_OUT := handleSuccesors (label, childrenCount, children)
	    val tmpList = List.map(LabelInfo.tmpGen (getLabelInfo label), fn v => (VVar v))
	    val S = diff(!ANTIC_OUT, tmpList)
	    val () = LabelInfo.anticIn' (getLabelInfo label) := diff(LabelInfo.expGen (getLabelInfo label), tmpList)
	    val () = List.foreach(S, fn s =>
					let
					    val values = case ValTable.lookup(s, VExp.hash s) of
									  NONE => []
									| SOME {values=(Value {vexps=values,...}),...} => !values 
					    val leader = findLeader(LabelInfo.expGen (getLabelInfo label), values)
					    val () = case leader of
							  NONE => (valInsert (LabelInfo.anticIn' (getLabelInfo label)) s)
						       |  SOME _ => ()
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
					 (*val () = prettyPrinter ()*)
					 (*val _ = doBuildSets_Phase2((Function.dominatorTree f))*)
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
