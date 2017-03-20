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
	 
(* Counter to provide ids for VExp.value *)
val nextValNum =
    let
	val ctr = ref 0
    in
	fn () => (ctr := !ctr + 1 ; !ctr)
    end
	
val nextValNumIter =
    let
	val ctr = ref 0
    in
	fn () => (ctr := !ctr + 1 ; !ctr)
    end	

fun append (r,x) = r := (!r)@[x]	
	
fun diagWithLabel label s =
  Control.diagnostics
      (fn display =>
          let open Layout
          in
              display (seq [Label.layout label, str ": ", str s])
          end)
      
fun diag s funcName =
  Control.diagnostics
      (fn display =>
          let open Layout
          in
              display (seq [str funcName, str ": ", str s])
          end)
      
structure VExp = 
   struct
   
   datatype t = 
            VConst of Const.t
	    | VPrimApp of {prim: Type.t Prim.t,
			   args: value ref vector,
                           targs: Type.t vector}
	    | VVar of Var.t
	and value = Value of {vexps: t list ref, id: int}
				 
   fun newValue () = Value {vexps=(ref []), id = nextValNum ()}
   fun nullValue () = Value {vexps=(ref []), id = (~1)}
			    
   fun valueEquals(xs: value, xs': value) =
       let
           val Value {id=id,...} = xs
           val Value {id=id',...} = xs'
       in
           id=id'
       end
   fun primValueListEquals (xs, xs') = Vector.equals (xs, xs', primValueEquals)
   and primValueEquals(xs: value ref, xs': value ref) =
       let
           val Value {id=id,...} = (!xs)
           val Value {id=id',...} = (!xs')
       in
           id=id'
       end
   and equals (e: t, e': t): bool =
       case (e, e') of
           (VConst c, VConst c') => Const.equals (c, c')
         | (VPrimApp {prim, args, ...},
            VPrimApp {prim = prim', args = args',...}) =>
	   Prim.equals (prim, prim') andalso primValueListEquals (args, args')	   
         | (VVar x, VVar x') => Var.equals (x, x')
         | _ => false
		    
   fun layoutValue v =
     let
	 open Layout
     in
	 case v of
	     Value {id=id,vexps=vexps} => seq  [(seq [str "", List.layout layout  (!vexps) ]) , Layout.str (Int.toString id)]
     end
   and primLayoutValue v =  
     let
	 open Layout
     in
	 case (!v) of
	     Value {id=id,vexps=vexps} => seq  [(seq [str "", List.layout layout  (!vexps) ]) , Layout.str (Int.toString id)]
     end	 
   and layout e =
       let
	 open Layout
	 fun layoutTuple xs = Vector.layout primLayoutValue xs
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
	     
       fun hashValueList (xs: value ref vector, w: Word.t): Word.t =
	 Vector.fold (xs, w, fn (x, w) => Word.xorb (w, hashValue (x,w)))
       and hashValue (xs: value ref, w: Word.t): Word.t =
           Word.xorb (w, hasher (!xs))
   in         
   val hash  = 
    fn (VConst c) => Const.hash c
     | (VPrimApp {args, ...}) => hashValueList (args, primApp) 
     | (VVar x) => Var.hash x
   end
   
   val hash = hash
		  
   end
       
open Exp Transfer VExp
(*	 
fun toPrettyValue value = case value of
			      Value {vexps=vexps, id=id} => Layout.toString (layoutValue value)
fun toPretty vexp = case vexp of
			(VConst c) => Const.toString c
		      | (VPrimApp {args,prim, ...}) =>
			Layout.toString
			       (Prim.layoutApp (prim, args, fn x =>
							       VExp.layoutValue x)) 
		      | (VVar x) => Var.toString x	 
*)
	 
structure ValTable =
struct
(* Keep a hash table of canonicalized Exps that are in scope. *)
val table: {hash: word, vexp: VExp.t, values: VExp.value } HashSet.t =
    HashSet.new {hash = #hash}	
	
fun sort args =
  let
      val ls = Vector.toList args
      fun le (v,v') = case (!v,!v') of
	                     ((VExp.Value {id=id,...}), (VExp.Value {id=id',...})) => (id <= id')
  in
      Vector.fromList (List.insertionSort (ls,le))
  end

fun canon vexp = case vexp of
                     VPrimApp {prim=prim,args=args,targs=targs} => if (Prim.isCommutative prim)
								   then VPrimApp {prim=prim,args = sort args, targs=targs}
								   else vexp
		   | _ => vexp
			      
fun lookup vexp =
  let
      val vexp = canon vexp
  in
      HashSet.peek
	  (table,VExp.hash vexp,
	   fn {vexp = vexp', ...} => VExp.equals (vexp, vexp'))
  end
      
fun lookupOrAddHelper (value, vexp, id) =
  let
      val hash = VExp.hash vexp
  in
      HashSet.lookupOrInsert
	  (table, hash,
	   fn {vexp = vexp', ...} => VExp.equals (vexp, vexp'),
	   fn () => {vexp = vexp,
		     hash = hash,
		     values = (Value {vexps = value, id = id})})
  end
      
fun lookupOrAdd vexp =
  let
      val vexp = canon vexp
      val x = lookup vexp
  in
      case x of
	  NONE  => lookupOrAddHelper(ref [vexp], vexp, nextValNum ())
	| SOME x => x 
  end
(*      
fun remove (vexp, hash) =
  HashSet.remove
      (table, hash,
       fn {vexp = vexp', ...} => VExp.equals (vexp, vexp'))
*)      
fun add (vexp, values, id) =
  let
      val vexp = canon vexp
      val () = append(values, vexp)
      val _ = lookupOrAddHelper(values, vexp, id)
  in
      ()
  end
end
(*
fun prettyPrinter ()  = HashSet.foreach (ValTable.table,
					     fn {hash, vexp, values} =>
						let 
						    val () = print ("HASH : " ^ (Word.toString hash) ^ " VEXP : " ^ (toPretty vexp) ^  " VALUE : " ^ (toPrettyValue values) )
						in
						    ()
						end)
*)					    
    
structure LabelInfo =
struct
datatype t = T of {dom: Label.t option ref,
                   predecessor: Block.t list ref,
				   successor:  Block.t list ref,
                       tmpGen: Var.t list ref,
					   killGen: Var.t list ref,
                       expGen: VExp.t list ref,
		       phiGen: Var.t list ref,
                       availOut: VExp.t list ref,
		       availIn: VExp.t list ref,
(*		       anticOut: VExp.t list ref,
*)		       anticIn: VExp.t list ref}
		      
fun new () = T {dom = ref NONE,
                predecessor = ref [],
				successor = ref [],
                tmpGen = ref [],
				killGen = ref [],
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
	val (predecessor', _) = make' #predecessor
	val (successor',successor) = make' #successor
    val (tmpGen', tmpGen) = make' #tmpGen
	val (killGen', killGen) = make' #killGen
    val (expGen', expGen) = make' #expGen
    val (phiGen', _) = make' #phiGen
    val (availOut', availOut) = make' #availOut
    val (_, _) = make' #availIn
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
	    val () = ValTable.add(VVar v,ref [], nextValNum ())
		val () = append(LabelInfo.killGen' (getLabelInfo label), v)
	    val () = append(LabelInfo.tmpGen' (getLabelInfo label), v)
	in
	    ()
	end
	    
      fun valInsert vs vexp =
	if List.contains(!vs, vexp, fn (vexp,vexp') =>
				       let
					   val v = ValTable.lookup vexp
					   val v' = ValTable.lookup vexp'
				       in
					   case (v,v') of
					       (SOME {values=value,...},SOME {values=value',...}) => VExp.valueEquals(value,value')
					     | (_,_) => false
				       end
			)
	then ()
	else append(vs,ValTable.canon vexp)
      (*
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
      *)		   
      fun handlePhiCondtions(v, label) =
	let
	    val () = ValTable.add(VVar v,ref [], nextValNum ())
	    val () = append(LabelInfo.phiGen' (getLabelInfo label), v)
	    val () = (valInsert (LabelInfo.availOut' (getLabelInfo label)) (VVar v))
	in
	    ()
	end
	    
      fun handleTransfer _ = ()
				 
      fun handleStatements(s, label) =
	let
	    val Statement.T {var=var, exp=exp,...} = s
	    val () =
		(case var of
		     NONE => () (*can there be statements without the RHS part where some things need to be done*)
		   | SOME var' => (case exp  of
				       Var v =>
				       (let
					   val (vexps,id) = case (ValTable.lookup (VVar v)) of
							   SOME {values=value,...} => (case value of
											   Value {vexps=vexps,id=id} => (vexps,id))
							 | NONE => (ref [], nextValNum ())
					   val () = ValTable.add(VVar var', vexps, id)
					   val () = (valInsert (LabelInfo.expGen' (getLabelInfo label)) (VVar v))
					   val () = append(LabelInfo.tmpGen' (getLabelInfo label), var')
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
											case (ValTable.lookup (VVar arg)) of
											    SOME {values=value,...} => ref value
											  | NONE => ref (VExp.newValue ()) (*filler will never happen*)
									      )
						    (*implement the canon exps case here*)
						    val exp = VPrimApp {args=valueList, prim=prim, targs=targs}
						    val {values=primValue,...} = ValTable.lookupOrAdd exp
						    val (Value {vexps=values,id=id}) = primValue
						    val () = ValTable.add(VVar var', values, id)
						    val _ = Vector.map(args, fn arg => (valInsert (LabelInfo.expGen' (getLabelInfo label)) (VVar arg) ))
						    val () = (valInsert (LabelInfo.expGen' (getLabelInfo label)) (VPrimApp {args=valueList, prim=prim, targs=targs}))
						    val () = append(LabelInfo.tmpGen' (getLabelInfo label), var')
						in
						    ()
						end)
					   else doNonFunctional (var', label)
				       end)
				     | _  => doNonFunctional (var', label) (* what are the other expressions that need to be taken care of *)
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
	    val () = diagWithLabel label "do args !!! phi condition"
            val _ = Vector.map(args, fn (a, _) => handlePhiCondtions(a, label)) 
	    val () = diagWithLabel label "do statements that is the expressions"
	    val _ = Vector.map(statements, fn s => handleStatements(s, label))
	    val () = diagWithLabel label "do the transfer which is empty for now"
	    val _ = handleTransfer transfer (* filler for now does nothing *)
	in
	    ()
	end
	    
      fun loopTree_Phase1 (blockTree, parent, labelNode, nodeBlock, bfsFunctionList) =
	let
	    val Tree.T (block, children) = blockTree
		val () = append(bfsFunctionList, block)
	    val label = Block.label block
	    (*val () = diagWithLabel label "buildset phase 1 started"*)
		val labelInfoObj = (getLabelInfo label)
		fun successors block = List.map(DirectedGraph.Node.successors (labelNode (Block.label block)), nodeBlock o DirectedGraph.Edge.to)
	    
		val () = LabelInfo.successor' labelInfoObj := (successors block)
		val _ = List.map(LabelInfo.successor labelInfoObj, fn s => let
		                                                              val succBlockLabel = Block.label s
		                                                           in
																   append(LabelInfo.predecessor' (getLabelInfo succBlockLabel),block)
																   end
		                ) 
	    val () = LabelInfo.dom' (getLabelInfo label) := parent

	    val () = LabelInfo.availOut' labelInfoObj := (case (LabelInfo.dom labelInfoObj) of
							      SOME domLabel => LabelInfo.availOut (getLabelInfo domLabel)
							   |   NONE         => [])
	    (*val () = diagWithLabel label "populating the gen lists for the block"*)
	    val () = doBuildSets_Phase1 (block)
	    (*val () = diagWithLabel label "over with this block"
	    val () = diagWithLabel label "lets see the gen list corresponding for this block"
	    val () = diagWithLabel label "dom"*)
	    (*
		val dom = case (LabelInfo.dom (getLabelInfo label)) of
			  NONE => "NONE"
			| SOME dom =>  (Layout.toString (Label.layout dom))
		*)
	    val () = diagWithLabel label "killOut"
	    val () = diagWithLabel label (Layout.toString (List.layout Var.layout (LabelInfo.killGen (getLabelInfo label))))
	    
		(*val () = diagWithLabel label dom
	    val () = diagWithLabel label "availOut"
	    val () = diagWithLabel label (Layout.toString (List.layout VExp.layout (LabelInfo.availOut (getLabelInfo label))))
	    val () = diagWithLabel label "phiGen"
	    val () = diagWithLabel label (Layout.toString (List.layout Var.layout (LabelInfo.phiGen (getLabelInfo label))))
	    val () = diagWithLabel label "expGen"
	    val () = diagWithLabel label (Layout.toString (List.layout VExp.layout (LabelInfo.expGen (getLabelInfo label))))
	    val () = diagWithLabel label "tempGem"
	    val () = diagWithLabel label (Layout.toString (List.layout Var.layout (LabelInfo.tmpGen (getLabelInfo label))))*)
					   
	    val () = Tree.Seq.foreach (children,fn child => loopTree_Phase1 (child, SOME label, labelNode, nodeBlock, bfsFunctionList))
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
	fun clean(lst1, killGen) =
	let
	    val killToVal = List.map(killGen, fn kill => let
		                                                 val v = case (ValTable.lookup (VVar kill)) of
							                                        NONE => ref (VExp.newValue ())
							                                       |SOME {values,...} => ref values
														 in
														    case (!v) of
															   VExp.Value{id=id,...} => id
														 end
				                )
		
    fun evaluateList [] = true
	  | evaluateList (l::ls) = l andalso evaluateList ls 
						
		fun checkValue v = case (!v) of 
		                     VExp.Value{vexps=vexps,id=id} => if List.contains(killToVal,id,Int.equals)
							                                  then false
															  else (evaluateList (List.map((!vexps), fn vexp => isValid vexp)))
						
	    and isValid vexp = case vexp of
				   (VPrimApp {args=args,...}) => evaluateList (Vector.toList (Vector.map(args , fn a => checkValue a)))
				 | (VVar v) => if List.contains(killGen,v,Var.equals)
                               then false
                               else true
                 |  _ => true						   
							   
							   
	    fun processedKills [] = []
	      | processedKills (l::ls) = (
		                              if(isValid l)
		                              then [l]@(processedKills ls)
									  else (processedKills ls)
									  )
	in
	    processedKills lst1
	end
   
      fun checkEquals [] [] = true
	| checkEquals (l::ls) (b::bs) = VExp.equals(l,b) andalso (checkEquals ls bs)
	| checkEquals _ _  = false 
				 
      fun findLeader( anticIn, exp) =
	let
	    val v = ValTable.lookup exp
				    
	    fun leader [] _ = []
	      | leader (l::ls) (SOME {values,...}) =  (case (ValTable.lookup l) of
							   NONE => leader ls v
							 | SOME {values = values',...} => if VExp.valueEquals(values, values')
											  then [l]
											  else leader ls v)
	      | leader _ _ = []
				 
	    val result = leader anticIn v
	in
	    result
	end
	    
      fun evaluateList [] = false
	| evaluateList (l::ls) = l orelse evaluateList ls 
						       
      fun phiTranslate (lst, block, succBlock) = 
	let
	    val () = diag "Phitranslate begins for ANTIC_IN " (Layout.toString (List.layout VExp.layout lst)) 
	    val Block.T {transfer,...} = block
	    val Block.T {args=fromVar',...} = succBlock
	    val toVar' = case transfer of
			     Goto {args,...} => args
			   | _ =>
			     let
				 val () = diag "transfer type " (Layout.toString (Transfer.layout transfer))
			     in
				 Vector.fromList [] 
			     end
	    fun varToValue v = case (ValTable.lookup (VVar v)) of
				   NONE => ref (VExp.nullValue ())(*remove this and make -1 case*)
				 | SOME {values,...} => ref values
	    val toVar = Vector.toList toVar'
	    val fromVar = List.map(Vector.toList fromVar', fn (arg,_) => arg)
	    val toValue = List.map(toVar, fn arg => varToValue arg)
	    val fromValue = List.map(fromVar, fn arg => varToValue arg)
	    val () = diag "fromVar " (Layout.toString (List.layout Var.layout fromVar)) 
	    val () = diag "toVar " (Layout.toString (List.layout Var.layout toVar)) 
	    val () = diag "fromValue " (Layout.toString (List.layout VExp.primLayoutValue fromValue)) 
	    val () = diag "toValue " (Layout.toString (List.layout VExp.primLayoutValue toValue)) 
	    val {intersect=intersect,...} = (List.set {equals=VExp.primValueEquals, layout=VExp.primLayoutValue})
						
	    fun translate vexp = case vexp of
				     (VVar v) => (case List.index(fromVar, fn v' => Var.equals(v,v')) of
						      NONE => vexp
						    | SOME i => (VVar (List.nth(toVar,i)))
						 )
				   | (VPrimApp {prim=prim, args=args, targs=targs}) =>
				     let
					 val intersection = intersect (Vector.toList args, fromValue)
					 fun translateArgs args = Vector.map(args, fn arg =>
										      (case List.index(fromValue, fn arg' => VExp.primValueEquals(arg,arg')) of
											   NONE => arg
											 | SOME i => (List.nth(toValue,i))
										      )
									    )
				     in
					 case intersection of
					     [] => vexp (* lookup or add *)
					   | _ => (let 
					              val newVexp = (VPrimApp {prim=prim, args=(translateArgs args), targs=targs})
					              val _ = ValTable.lookupOrAdd(newVexp)
						  in
						      newVexp
						  end)								  
				     end
				   | x  => x 
	in
	    case transfer of
		Goto {...} => List.map(lst, translate)
	      | _ => [] 
	end
	    
      fun handleSuccesors (block, childrenCount, children) =
	if childrenCount=1
	then
	    let
		val () = diag  "Succesor count for block case 1 " (Int.toString childrenCount)
		val succBlock = List.first children
		val succBlockLabel = Block.label succBlock
	    in
		phiTranslate (LabelInfo.anticIn (getLabelInfo (succBlockLabel)), block, succBlock)
	    end
	else if (childrenCount>1)
	then
	    (
	      let
		  val () = diag "Succesor count for block case 2 " (Int.toString childrenCount)
		  val worklist = ref children
		  val block = List.pop worklist
		  val label = Block.label block
		  val ANTIC_OUT = ref []
		  val () = ANTIC_OUT := LabelInfo.anticIn (getLabelInfo label)
		  val () = diag "ANTIC_OUT before removals" (Layout.toString (List.layout VExp.layout (!ANTIC_OUT)))
		  fun handleWorkList ANTIC_OUT (ref []) = !ANTIC_OUT
		    | handleWorkList ANTIC_OUT worklist =
		      (
			let
			    val block = List.pop worklist
						 
			    val b'label = Block.label block 
			    val () =
				List.foreach(!ANTIC_OUT, fn e => 
							    let
								val {remove=remove,...} = (List.set {equals=VExp.equals, layout=VExp.layout})
								val () =
								    case findLeader (LabelInfo.anticIn (getLabelInfo b'label), e)  of 
									[] => ANTIC_OUT := (remove (!ANTIC_OUT, e))
								      | _ => ()  
							    in
								()
							    end
					    )
			in
			    (handleWorkList ANTIC_OUT worklist)
			end
		      )
		  val () = diag "ANTIC_OUT after removals" (Layout.toString (List.layout VExp.layout (!ANTIC_OUT)))
	      in
		  (handleWorkList ANTIC_OUT worklist) 
	      end
	    ) 
	else (let 
		 val () = diag "Succesor count for block case 3 " (Int.toString childrenCount)
	     in
		 []
	     end)
		 
      fun loopTree_Phase2 (block) =
	let
	    
	    val label = Block.label block
	    val () = diagWithLabel label "starting with block for this iteration"
		val labelInfoObj = (getLabelInfo label)
	    val old = (LabelInfo.anticIn labelInfoObj)
	    val () = diagWithLabel label  (Layout.toString (List.layout VExp.layout old))
	    val ANTIC_OUT = ref []
        
		val blockSuccessors = LabelInfo.successor labelInfoObj
	    val () = ANTIC_OUT := handleSuccesors (block, List.length blockSuccessors,  blockSuccessors)
	    val () = diag "ANTIC_OUT "  (Layout.toString (List.layout VExp.layout (!ANTIC_OUT)))
	    val tmpList = List.map(LabelInfo.tmpGen labelInfoObj, fn v => (VVar v))
	    val () = diag "tmpList "  (Layout.toString (List.layout VExp.layout tmpList))
	    val S = diff(!ANTIC_OUT, tmpList)
	    val () = diag "S "  (Layout.toString (List.layout VExp.layout S))
	    val () = LabelInfo.anticIn' labelInfoObj := diff(LabelInfo.expGen labelInfoObj, tmpList)
	    val () = diag "ANTIC_IN "  (Layout.toString (List.layout VExp.layout (LabelInfo.anticIn labelInfoObj)))
	    val () = List.foreach(S, fn s =>
					let
					    val leader = findLeader(LabelInfo.expGen labelInfoObj, s)
					    val () = case leader of
							 [] => (valInsert (LabelInfo.anticIn' labelInfoObj) s)
						      |  _ => ()
					in
					    ()
					end
				 )
	    val () = diag "ANTIC_IN After inserts "  (Layout.toString (List.layout VExp.layout (LabelInfo.anticIn (getLabelInfo label))))		 
	    val () = LabelInfo.anticIn' (getLabelInfo label) := clean(LabelInfo.anticIn (getLabelInfo label), (LabelInfo.killGen (getLabelInfo label)))
	    val () = diag "ANTIC_IN After Clean "  (Layout.toString (List.layout VExp.layout (LabelInfo.anticIn (getLabelInfo label))))

	    val () = diagWithLabel label "done with block for this iteration"
					   
	in
	  if (checkEquals old  (LabelInfo.anticIn (getLabelInfo label))) 
	  then false  
	  else true
	end

	fun doBuildSets_Phase2 (dfsFunctionList) =
	let
	    val iterNumber = nextValNumIter ()
	    val () = diag "Starting iteration " (Int.toString iterNumber)
	    val isChanged = if evaluateList(List.map(dfsFunctionList, fn block => loopTree_Phase2 block))
		                then doBuildSets_Phase2 (dfsFunctionList)
						else false
			    
				
	    val () = diag "Fininshing iteration " (Int.toString iterNumber)
	in
	    isChanged 
	end
	
	fun eliminateStatements s block = 
	   let
	     val Statement.T {var=var, exp=exp, ty=ty} = s
		 val label = Block.label block
		 val labelInfoObj = (getLabelInfo label)
		 in
			(case var of
						  NONE => s
						| SOME v => (case exp of
										PrimApp {prim=prim,...}=> 
												   (let
												      val () = diag "statement working on " (Layout.toString (Statement.layout s))
												      val exp' = if (Prim.isFunctional prim) 
													             then 
																     (let
																	      val () = diag "availOut" (Layout.toString (List.layout VExp.layout (LabelInfo.availOut labelInfoObj)))
																		  val () = diag "exp" (Layout.toString (VExp.layout (VVar v)))
																	      val sList' = findLeader(LabelInfo.availOut labelInfoObj, VVar v)
																		  val () = diag "availOut" (Layout.toString (List.layout VExp.layout sList'))
																		  
																		  
																	  in
																	    (case sList' of
																		 [] => exp
																		| [(VVar s')] =>   if VExp.equals(VVar s',VVar v)
																							then exp
																							else (Var s') 
																		| _ => exp)
																	  end)
																 else exp
													val () = diag "changed exp " (Layout.toString (Exp.layout exp'))
													in
													  Statement.T {var=var, exp=exp', ty=ty}
													end)
										| _ => s)
			)
	     
	   end
	
	fun eliminate block = 
	   let
	    val () = diag "eliminate block " (Layout.toString (Block.layout block))
		val Block.T {args,label,statements,transfer} = block
		val statements' = Vector.map(statements, fn s => eliminateStatements s block)
		val () = diag "" "eliminate done for the block"
	   in
		Block.T {args=args, label=label, statements=statements', transfer=transfer}
	   end
	    
      val globalLabel = Label.fromString "globals"
      val () = diag "Number of globals" (Int.toString (Vector.length globals))
      val () = diag "globals" (Layout.toString (Vector.layout Statement.layout globals))
      val _ = Vector.map(globals, fn s => handleStatements(s, globalLabel))
	      
   
   

	  val functions = List.map(functions,fn f =>
				 let
				 val {args, blocks, mayInline, name, raises, returns, start} = Function.dest f
				 val dfsFunctionList = ref []
				 val bfsFunctionList = ref []
				 val () = Function.dfs(f,fn b => fn () => append(dfsFunctionList,b))
				 val () = diag "function name" (Func.toString name)
				 (*val () = diag "starting buildsets phase 1" "List.map(functions)"*)
				 val {labelNode=labelNode, nodeBlock=nodeBlock, ...} = Function.controlFlow f
				 val () = loopTree_Phase1 ((Function.dominatorTree f), NONE, labelNode, nodeBlock, bfsFunctionList)
				 (*val () = diag "done with buildsets phase 1" "List.map(functions)"*)
				 val () = diag "dfs for function blocks " (Layout.toString (List.layout Block.layout (!dfsFunctionList)))
				 val () = diag "done with buildsets phase 1" "List.map(functions)"
				 (*val () = prettyPrinter ()*)
				 val () = diag "starting buildsets phase 2" "List.map(functions)"
				 val _ = doBuildSets_Phase2(!dfsFunctionList)
				 val () = diag "done with buildsets phase 2" "List.map(functions)"
				 
				 val blocks = Vector.map(Vector.fromList (!bfsFunctionList), fn block => eliminate block)
					
				 in
				 Function.new {args = args,
						   blocks = blocks,
						   mayInline = mayInline,
						   name = name,
						   raises = raises,
						   returns = returns,
						   start = start}
				 end)	 
      val _ = HashSet.foreach (ValTable.table,
			       fn {vexp=vexp, values=values,...} =>
				  let 
				      val () = diag "Table" (Layout.toString (Layout.seq [VExp.layout vexp, VExp.layoutValue values]))
				  in
				      ()
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
