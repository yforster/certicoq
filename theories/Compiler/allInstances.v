Require Export Common.certiClasses.
Require Export Common.certiClasses2.
Require Export L2.instances.
Require Export L1g.instances.
Require Export L2_5.instances.
Require Export L2d.instances.
Require Export L2k.instances.
Require Export L3.instances.
Require Export L4.instances.
Require Export L6.instances.


Set Template Cast Propositions.

                
Open Scope Z_scope.
Require Import ZArith.


Require Import Common.Common.
Require Import String.
Open Scope string_scope.


Ltac computeExtract certiL4 f:=
(let t:= eval compute in (translateTo (cTerm certiL4) f) in 
     match t with
       |Ret ?xx => exact xx
     end).



Quote Recursively Definition One := 1%positive.
(*
Definition One6 : cTerm certiL6.
(let t:= eval vm_compute in (translateTo (cTerm certiL6) One) in 
match t with
|Ret ?xx => exact xx
end).
Defined. *)
Import CertiCoq.Libraries.maps_util.

Definition ext_comp := fun prog =>
  let t := (translateTo (cTerm certiL6) prog) in
  match t with
  | Ret xx => xx
  | _ => ((M.empty _, M.empty _, M.empty _, M.empty _) , (M.empty _, cps.Ehalt 1%positive))
  end.
 
Require Import L6_to_Clight.

Require Import compcert.lib.Maps.
Definition argsIdent:positive := 26.
Definition allocIdent:positive := 28.
Definition limitIdent:positive := 29.
Definition gcIdent:positive := 80.
Definition mainIdent:positive := 81.
Definition bodyIdent:positive := 90.
Definition threadInfIdent:positive := 31.
Definition tinfIdent:positive := 91.
Definition heapInfIdent:positive := 95.
Definition numArgsIdent:positive := 97.
Definition isptrIdent:positive := 82.
Definition caseIdent:positive := 83.


Definition compile_L7 (t : cTerm certiL6) : L5_to_L6.nEnv * Clight.program * Clight.program :=
  let '((_, cenv , nenv, fenv), (_, prog)) := t in
  let p := compile argsIdent allocIdent limitIdent gcIdent mainIdent bodyIdent threadInfIdent tinfIdent heapInfIdent numArgsIdent isptrIdent caseIdent
                   prog cenv nenv in
  (fst (fst p), stripOption mainIdent (snd (fst p)), stripOption mainIdent (snd p)).




Definition compile_opt_L7 p  :=
  match p with
  | Ret p => Ret (compile_L7 p)
  | Exc s => Exc s
  end.

Definition compile_template_L4 (p : program) : exception (cTerm certiL4) :=
  translateTo (cTerm certiL4) p.

Definition compile_template_L7 (p : program) : exception (L5_to_L6.nEnv * Clight.program * Clight.program)  :=
  compile_opt_L7 (translateTo (cTerm certiL6) p).

Open Scope positive_scope.
  



Require Import L6.cps L6.cps_show.

Definition show_exn  (x : exceptionMonad.exception (cTerm certiL6)) : string :=
  match x with
  | exceptionMonad.Exc s => s
  | exceptionMonad.Ret ((p,cenv, nenv, fenv), (g, e)) => L6.cps_show.show_exp nenv cenv true e
  end.

Require Import L6_to_Clight.
Require Import compcert.lib.Maps.

Require Import L6.cps L6.cps_show. 
(* copy of L6.instances.L5a_comp_L6 *)
(* Definition L5a_comp_L6 (v:(ienv * L4.L5a.cps)): ((L6.eval.prims * cEnv * nEnv)* (L6.eval.env * L6.cps.exp)):= 
    match v with
        | pair venv vt => 
          let '(cenv, nenv, next_cTag, next_iTag, t) := L6.L5_to_L6.convert_top default_cTag default_iTag fun_fTag kon_fTag (venv, vt) in
          let '(cenv',nenv', t') :=  L6.closure_conversion.closure_conversion_hoist
                                       bogus_cloTag
                                       (L6.shrink_cps.shrink_top t) 
                                       next_cTag
                                       next_iTag
                                       cenv nenv in
          ((M.empty _ , (add_cloTag bogus_cloTag bogus_cloiTag cenv'), nenv'),  (M.empty _,  L6.shrink_cps.shrink_top t')) 
    end.
 *)

  
Require Import Benchmarks.Binom
        Benchmarks.Color
        Benchmarks.vs.




(*  Quote Recursively Definition vs := vs.main_h.  (*ce_example_ent*) *)
(* Quote Recursively Definition binom := Binom.main.    *)
(* Quote Recursively Definition graph_color := Color.ex_2.  (*(Color.run G16)*)    *)
Quote Recursively Definition graph_color := 2.  (*(Color.run G16)*)   




  



(* Definition binom5 := Eval native_compute in (translateTo (cTerm certiL5a) binom). *)
Definition color5 := Eval native_compute in (translateTo (cTerm certiL5) graph_color).   
(* Definition vs5 := Eval native_compute in (translateTo (cTerm certiL5a) vs).  *)


 

Definition printProg := fun prog file => L6_to_Clight.print_Clight_dest_names (snd prog) (cps.M.elements (fst prog)) file.

(* Definition test := printProg (compile_L7 (ext_comp vs)) "output/vs_h.c".      *)
(*  Definition test := printProg (compile_L7 (ext_comp graph_color)) "output/color.c".    *)




 Section TEST_L6.
(*  This can be used to test L6 (using an L5 program, extract to ML and run in ocaml to translate to L6 and then run using L6 executable semantics : *)
Require Import  ExtLib.Data.String. 
(* Multistep *)
Fixpoint mstep_L6  (x : (cTerm certiL6)) (n:nat) :=
  match n with
    | O =>
      Ret x
    | S n' =>
      let '((p,cenv, nenv, fenv), (rho, e)) := x in
      (match (L6.eval.sstep_f p cenv rho e) with
         | Ret (rho', e') => mstep_L6 ((p, cenv, nenv, fenv), (rho',e')) n'
         | Exc s => Exc ("Error :"++s++" at "++(nat2string10 n)++" from end")%string
       end)
  end.

Definition print_BigStepResult_L6 p  n:=
  let '((prim,cenv, nenv, fenv), (rho, e)) := p in
  L7.L6_to_Clight.print (
      match (L6_evaln n p) with
      | Error s _ => s
      | OutOfTime (_, (rho', e')) => "Out of time:"++ (show_env nenv cenv false rho')++ (show_exp nenv cenv false e')
      | Result v => show_val nenv cenv false v
      end).

 Definition comp_L6 p := match p
                          with
                            | Exc s => Exc s
                            | Ret v =>  L6.instances.certiL5_t0_L6 v                                           
                        end.

Definition comp_to_L6:= fun p =>
                       comp_L6 (translateTo (cTerm certiL5) p).


Definition testL6 := match comp_L6 color5 with
                   | Ret ((pr,cenv,nenv), (env, t)) => print_BigStepResult_L6 ((pr,cenv,nenv), (env, t)) 30%nat 
                   | _ =>   L7.L6_to_Clight.print ("Failed during comp_L6")
                   end.

(*Extraction "test_color_eg2.ml" testL6.  *)

 End TEST_L6.




 

