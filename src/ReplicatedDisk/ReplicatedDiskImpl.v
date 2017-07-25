Require Import POCS.

Require Import TwoDisk.TwoDiskAPI.
Require Import ReplicatedDisk.ReplicatedDiskAPI.
Require Import ReplicatedDisk.TwoDiskProgSpec.

Module RD.

  Section ReplicatedDisk.

    (* The replicated disk implementation works for any implementation of two
     * disks - [Interface] already captures the implementation and all the
     * correctness proofs needed here. *)
    Variable (td:Interface TD.API).

    (**
     * Implementation of the replicated disk API.
     *)

    Definition Read (a:addr) : prog block :=
      mv0 <- Prim td (TD.Read d0 a);
      match mv0 with
      | Working v => Ret v
      | Failed =>
        mv2 <- Prim td (TD.Read d1 a);
        match mv2 with
        | Working v => Ret v
        | Failed => Ret block0
        end
      end.

    Definition Write (a:addr) (b:block) : prog unit :=
      (* Fill in your implementation here. *)
      Ret tt.

    Definition write_read_check (a : addr) (b : block) : prog block :=
      _ <- Write a b;
      b' <- Read a;
      Ret b'.

    Definition DiskSize : prog nat :=
      msz <- Prim td (TD.DiskSize d0);
      match msz with
      | Working sz => Ret sz
      | Failed =>
        msz <- Prim td (TD.DiskSize d1);
        match msz with
        | Working sz => Ret sz
        | Failed => Ret 0
        end
      end.

    Definition DiskSizeInit : prog (option nat) :=
      sz1 <- Prim td (TD.DiskSize d0);
      sz2 <- Prim td (TD.DiskSize d1);
      match sz1 with
      | Working sz1 =>
        match sz2 with
        | Working sz2 =>
          if sz1 == sz2 then Ret (Some sz1) else Ret None
        | Failed => Ret (Some sz1)
        end
      | Failed =>
        match sz2 with
        | Working sz2 => Ret (Some sz2)
        | Failed => Ret None
        end
      end.

    (* Initialize block a *)
    Fixpoint init_at (a:nat) : prog unit :=
      match a with
      | 0 => Ret tt
      | S a =>
        _ <- Prim td (TD.Write d0 a block0);
        _ <- Prim td (TD.Write d1 a block0);
        init_at a
      end.

    (* Recursively initialize every disk block *)
    Definition Init : prog InitResult :=
      size <- DiskSizeInit;
      match size with
      | Some sz =>
        _ <- init_at sz;
        Ret Initialized
      | None =>
        Ret InitFailed
      end.


    (**
     * Helper lemmas and tactics for proofs.
     *)

    (* As the final step in giving the correctness of the replicated disk
    operations, we prove recovery specs that include the replicated disk Recover
    function. *)

    Lemma exists_tuple2 : forall A B (P: A * B -> Prop),
        (exists a b, P (a, b)) ->
        (exists p, P p).
    Proof.
      intros.
      repeat deex; eauto.
    Qed.

    (* we use a focused hint database for rewriting because autorewrite becomes
           very slow with just a handful of patterns *)
    Create HintDb rd.

    Ltac simplify :=
      repeat match goal with
             | |- forall _, _ => intros
             | _ => deex
             | _ => destruct_tuple
             | |- _ /\ _ => split; [ solve [auto] | ]
             | |- _ /\ _ => split; [ | solve [auto] ]
             (* TODO: extract the match pattern inside the exists on a0 and use
                    those names in exists_tuple *)
             | |- exists (_: _*_), _ => apply exists_tuple2
             | _ => progress simpl in *
             | _ => progress safe_intuition
             | _ => progress subst
             | _ => progress autounfold with rd in *
             | _ => progress autorewrite with rd in *
             | [ u: unit |- _ ] => destruct u
             | [ crashinv: _ -> Prop |- _ ] =>
               match goal with
               | [ H: forall _, _ -> crashinv _ |-
                           crashinv _ ] =>
                 eapply H
               end
             end.

    Ltac finish :=
      repeat match goal with
             | _ => solve_false
             | _ => congruence
             | _ => solve [ intuition (subst; eauto; try congruence) ]
             | _ =>
               (* if we can solve all the side conditions automatically, then it's
               safe to run descend *)
               descend; intuition eauto;
               lazymatch goal with
               | |- prog_spec _ _ _ _ => idtac
               | _ => fail
               end
             end.

    Ltac step :=
      step_prog; simplify; finish.

    Ltac start := intros;
                  match goal with
                  | |- prog_spec _ _ (_ <- _; _) _ =>
                    eapply compose_recovery; eauto; simplify
                  end.

    Hint Unfold TD.wipe : rd.

    Implicit Type (state:TD.State).


    (**
     * Specifications and proofs about our implementation of the replicated disk API,
     * without considering our recovery.
     *)

    Lemma both_disks_not_missing : forall (state: TD.State),
        TD.disk0 state ?|= missing ->
        TD.disk1 state ?|= missing ->
        False.
    Proof.
      destruct state; simpl; intros.
      destruct disk0, disk1; simpl in *; eauto.
    Qed.
    Hint Resolve both_disks_not_missing : false.

    Theorem Read_ok : forall a,
        prog_spec
          (fun d state =>
             {|
               pre := TD.disk0 state ?|= eq d /\
                      TD.disk1 state ?|= eq d;
               post :=
                 fun r state' =>
                   d a ?|= eq r /\
                   TD.disk0 state' ?|= eq d /\
                   TD.disk1 state' ?|= eq d;
               recover :=
                 fun _ state' =>
                   TD.disk0 state' ?|= eq d /\
                   TD.disk1 state' ?|= eq d;
             |})
          (Read a)
          (irec td)
          (interface_abs td).
    Proof.
      unfold Read.

      step.

      destruct r; step.
      destruct r; step.
    Qed.

    Hint Resolve Read_ok.


    Theorem Write_ok : forall a b,
        prog_spec
          (fun d state =>
             {|
               pre :=
                 TD.disk0 state ?|= eq d /\
                 TD.disk1 state ?|= eq d;
               post :=
                 fun r state' =>
                   r = tt /\
                   (* Fill in your postcondition here *)
                   True;
               recover :=
                 fun _ state' =>
                   (* Fill in your recovery condition here *)
                   True;
             |})
          (Write a b)
          (irec td)
          (interface_abs td).
    Proof.
      unfold Write.

      step.

      (* Prove your write implementation meets your postcondition and recovery condition. *)
    Qed.

    Hint Resolve Write_ok.


    Theorem write_read_check_ok : forall a b,
        prog_spec
          (fun d state =>
             {|
               pre :=
                 a < size d /\
                 TD.disk0 state ?|= eq d /\
                 TD.disk1 state ?|= eq d;
               post :=
                 fun r state' =>
                   r = b /\
                   TD.disk0 state' ?|= eq (diskUpd d a b) /\
                   TD.disk1 state' ?|= eq (diskUpd d a b);
               recover :=
                 fun _ state' =>
                   True;
             |})
          (write_read_check a b)
          (irec td)
          (interface_abs td).
    Proof.
      unfold write_read_check.
      step.
      (* Prove that write_read_check meets its postcondition  *)
      all: pocs_admit.
    Qed.

    Hint Resolve write_read_check_ok.


    Theorem DiskSize_ok :
      prog_spec
        (fun '(d_0, d_1) state =>
           {|
             pre :=
               TD.disk0 state ?|= eq d_0 /\
               TD.disk1 state ?|= eq d_1 /\
               size d_0 = size d_1;
             post :=
               fun r state' =>
                 r = size d_0 /\
                 r = size d_1 /\
                 TD.disk0 state' ?|= eq d_0 /\
                 TD.disk1 state' ?|= eq d_1;
             recover :=
               fun _ state' =>
                 TD.disk0 state' ?|= eq d_0 /\
                 TD.disk1 state' ?|= eq d_1;
           |})
        (DiskSize)
        (irec td)
        (interface_abs td).
    Proof.
      unfold DiskSize.

      step.

      destruct r; step.
      destruct r; step.
    Qed.

    Hint Resolve DiskSize_ok.


    Definition equal_after a (d_0 d_1: disk) :=
      size d_0 = size d_1 /\
      forall a', a <= a' -> d_0 a' = d_1 a'.

    Lemma le_eq_or_S_le : forall n m,
        n <= m ->
        n = m \/
        S n <= m /\ n <> m.
    Proof.
      intros.
      omega.
    Qed.

    Lemma equal_after_diskUpd : forall a d_0 d_1 b,
        equal_after (S a) d_0 d_1 ->
        equal_after a (diskUpd d_0 a b) (diskUpd d_1 a b).
    Proof.
      unfold equal_after; intuition.
      autorewrite with upd; eauto.
      apply le_eq_or_S_le in H; intuition subst.
      destruct (lt_dec a' (size d_0)); autorewrite with upd.
      assert (a' < size d_1) by congruence; autorewrite with upd; auto.
      assert (~a' < size d_1) by congruence; autorewrite with upd; auto.
      autorewrite with upd; eauto.
    Qed.
    Hint Resolve equal_after_diskUpd.

    Theorem init_at_ok : forall a,
        prog_spec
          (fun '(d_0, d_1) state =>
             {| pre :=
                  TD.disk0 state ?|= eq d_0 /\
                  TD.disk1 state ?|= eq d_1 /\
                  equal_after a d_0 d_1;
                post :=
                  fun _ state' =>
                 (* Fill in your postcondition here *)
                    exists d_0' d_1': disk,
                   True;

                recover :=
                  fun _ state' => True;
             |})
          (init_at a)
          (irec td)
          (interface_abs td).
    Proof.
      (* Prove your init_at implementation meets your postcondition *)
      all: pocs_admit.
    Qed.

    Hint Resolve init_at_ok.


    Theorem DiskSizeInit_ok :
        prog_spec
          (fun '(d_0, d_1) state =>
             {| pre :=
                  TD.disk0 state ?|= eq d_0 /\
                  TD.disk1 state ?|= eq d_1;
                post :=
                   fun r state' =>
                    exists d_0' d_1',
                      TD.disk0 state' ?|= eq d_0' /\
                      TD.disk1 state' ?|= eq d_1' /\
                      match r with
                      | Some sz => size d_0' = sz /\ size d_1' = sz
                      | None => True
                      end;
                recover :=
                  fun _ state' => True;
             |})
          (DiskSizeInit)
          (irec td)
          (interface_abs td).
    Proof.
      unfold DiskSizeInit.
      step.
      step.
      destruct r; descend; intuition eauto.
      - destruct r; try step.
        destruct (v == v0); step.
      - destruct r; step.
    Qed.

    Hint Resolve DiskSizeInit_ok.


    Lemma equal_after_0_to_eq : forall d_0 d_1,
        equal_after 0 d_0 d_1 ->
        d_0 = d_1.
    Proof.
      unfold equal_after; intuition.
      eapply diskMem_ext_eq.
      extensionality a'.
      eapply H1; omega.
    Qed.

    Lemma equal_after_size : forall d_0 d_1,
        size d_0 = size d_1 ->
        equal_after (size d_0) d_0 d_1.
    Proof.
      unfold equal_after; intuition.
      assert (~a' < size d_0) by omega.
      assert (~a' < size d_1) by congruence.
      autorewrite with upd; eauto.
    Qed.

    Hint Resolve equal_after_size.
    Hint Resolve equal_after_0_to_eq.

    Theorem Init_ok :
        prog_spec
          (fun '(d_0, d_1) state =>
             {| pre :=
                  TD.disk0 state ?|= eq d_0 /\
                  TD.disk1 state ?|= eq d_1;
                post :=
                  fun r state' =>
                 (* Fill in your postcondition here *)
                   True;

                recover :=
                  fun _ state' => True;
             |})
          (Init)
          (irec td)
          (interface_abs td).
    Proof.
      (* Prove your init implementation meets your postcondition *)
      all: pocs_admit.
    Qed.

    Hint Resolve Init_ok.


    (**
     * Recovery implementation.
     *)


    Definition Recover : prog unit :=
      Ret tt.


    (* Now we gather up the implementation and all the correctness proofs,
     * expressing them in terms of the high-level API in D.API. *)

    (* First, we prove some lemmas that re-express the D.API semantics in more
     * convenient terms (in some cases, just for the sake of the automation). *)

    Lemma read_step : forall a (state state':RD.State) b,
        state a ?|= eq b ->
        state' = state ->
        RD.step (RD.Read a) state b state'.
    Proof.
      intros; subst.
      constructor; auto.
      intros.
      replace (state a) in *; auto.
    Qed.

    Lemma write_step : forall a b (state state':RD.State) u,
        state' = diskUpd state a b ->
        RD.step (RD.Write a b) state u state'.
    Proof.
      intros; subst.
      destruct u.
      econstructor; eauto.
    Qed.

    Lemma disk_size_step : forall (state state':RD.State) r,
        r = size state ->
        state' = state ->
        RD.step (RD.DiskSize) state r state'.
    Proof.
      intros; subst.
      econstructor; eauto.
    Qed.

    Hint Resolve read_step write_step disk_size_step.




    (**
     * The proof will require a refinement; we build one up based on the two
     * disk state.
     *)

    Definition abstraction_f (state:TD.State) : RD.State :=
      match state with
      | TD.Disks (Some d) _ _ => d
      | TD.Disks None (Some d) _ => d
      | _ => empty_disk (* impossible *)
      end.

    Definition rd_invariant (state:TD.State) :=
      match state with
      | TD.Disks (Some d_0) (Some d_1) _ =>
        d_0 = d_1
      | _ => True
      end.

    Definition rd_layer_abstraction (state:TD.State) (state':RD.State) :=
      rd_invariant state /\
      state' = abstraction_f state.

    (* We re-express the abstraction and invariant's behavior in terms of the
       maybe holds (m ?|= F) statements in all of our specifications. *)

    Ltac crush :=
      intros; repeat match goal with
                     | [ state: TD.State |- _ ] =>
                       destruct state; simpl in *
                     | _ => destruct matches in *
                     | _ => eauto
                     end.

    Lemma invariant_to_disks_eq0 : forall state,
        rd_invariant state ->
        TD.disk0 state ?|= eq (abstraction_f state).
    Proof.
      crush.
    Qed.

    Lemma invariant_to_disks_eq1 : forall state,
        rd_invariant state ->
        TD.disk1 state ?|= eq (abstraction_f state).
    Proof.
      crush.
    Qed.

    Lemma disks_eq_to_invariant : forall state d,
        TD.disk0 state ?|= eq d ->
        TD.disk1 state ?|= eq d ->
        rd_invariant state.
    Proof.
      crush.
    Qed.

    Lemma disks_eq_to_abstraction : forall state d,
        TD.disk0 state ?|= eq d ->
        TD.disk1 state ?|= eq d ->
        d = abstraction_f state.
    Proof.
      crush.
      solve_false.
    Qed.

    Lemma disks_eq_to_abstraction' : forall state d,
        TD.disk0 state ?|= eq d ->
        TD.disk1 state ?|= eq d ->
        abstraction_f state = d.
    Proof.
      intros.
      symmetry; eauto using disks_eq_to_abstraction.
    Qed.

    Hint Resolve invariant_to_disks_eq0 invariant_to_disks_eq1.
    Hint Resolve
         disks_eq_to_invariant
         disks_eq_to_abstraction
         disks_eq_to_abstraction'.

    (* Finally, we put together the pieces of the [Interface]. Here we also
     * convert from our specificatiosn above to the exact form that an Interface
     * uses; the proofs are automatic after defining the lemmas above about D.step
     * and the layer refinement. *)

    Definition d_op_impl T (op:RD.Op T) : prog T :=
      match op with
      | RD.Read a => Read a
      | RD.Write a b => Write a b
      | RD.DiskSize => DiskSize
      end.

    Definition rd_abstraction : Abstraction RD.State :=
      abstraction_compose
        (interface_abs td)
        {| abstraction := rd_layer_abstraction; |}.

    Definition impl : InterfaceImpl RD.Op :=
      {| op_impl := d_op_impl;
         recover_impl := _ <- irec td; Recover;
      init_impl := then_init (iInit td) (Init) |}.

    Theorem state_some_disks : forall state,
        exists d_0 d_1,
          TD.disk0 state ?|= eq d_0 /\
          TD.disk1 state ?|= eq d_1.
    Proof.
      destruct state.
      destruct disk0, disk1; simpl; eauto.
      exfalso; eauto.
    Qed.

    Theorem rd_crash_effect_valid :
      crash_effect_valid {| abstraction := rd_layer_abstraction; |}
                         TD.wipe (fun (state state':RD.State) => state' = state).
    Proof.
      econstructor; unfold TD.wipe; intuition (subst; eauto).
    Qed.

    Theorem rd_layer_abstraction_f : forall state,
        rd_invariant state ->
        rd_layer_abstraction state (abstraction_f state).
    Proof.
      unfold rd_layer_abstraction; intuition.
    Qed.

    Hint Resolve rd_layer_abstraction_f.

    Definition rd : Interface RD.API.
      unshelve econstructor.
      - exact impl.
      - exact rd_abstraction.
      - intros.
        all: pocs_admit.
      - 
        all: pocs_admit.
      - 
        all: pocs_admit.

        Grab Existential Variables.
        all: auto.


        all: pocs_admit.
    Defined.

  End ReplicatedDisk.

End RD.

Print Assumptions RD.rd.
