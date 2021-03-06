Require Import POCS.
Require Import RemappedDisk.RemappedDiskAPI.
Require Import BadSectorDisk.BadSectorAPI.

Import BadSectorDisk.
Import RemappedDisk.

Module RemappedDisk.

  Section Implementation.

    Variable (bd : Interface BadSectorDisk.API).

    Definition read (a : addr) : prog block :=
      bs <- Prim bd (GetBadSector);
      if a == bs then
        len <- Prim bd (BadDiskSize);
        Prim bd (BadRead (len-1))
      else
        Prim bd (BadRead a).

    Definition write (a : addr) (b : block) : prog unit :=
      (* Fill in your implementation here. *)
      Prim bd (BadWrite a b).

    Definition diskSize : prog nat :=
      len <- Prim bd (BadDiskSize);
      Ret (len - 1).

    Definition rd_op_impl T (op: RemappedDisk.Op T) : prog T :=
      match op with
      | Read a => read a
      | Write a b => write a b
      | DiskSize => diskSize
      end.

    Definition init : prog InitResult :=
      len <- Prim bd (BadDiskSize);
      if len == 0 then
        Ret InitFailed
      else
        bs <- Prim bd (GetBadSector);
        if (lt_dec bs len) then
          Ret Initialized
        else
          Ret InitFailed.

    Definition impl : InterfaceImpl RemappedDisk.Op :=
      {| op_impl := rd_op_impl;
         recover_impl := Ret tt;
         init_impl := then_init (iInit bd) init; |}.

    Inductive remapped_abstraction (bs_state : BadSectorDisk.State) (rd_disk : RemappedDisk.State) : Prop :=
      | RemappedAbstraction :
        let bs_disk := stateDisk bs_state in
        let bs_addr := stateBadSector bs_state in
        forall
          (* Fill in the rest of your abstraction here. *)
          (* Hint 1: What should be true about the non-bad sectors? *)
          (* Hint 2: What should be true about the bad sector? *)
          (* Hint 3: What if the bad sector address is the last address? *)
          (* Hint 4: What if the bad sector address is past the end of the disk? *)
          (Hsize : size bs_disk = size rd_disk + 1),
        remapped_abstraction bs_state rd_disk.

    Definition abstr : Abstraction RemappedDisk.State :=
      abstraction_compose
        (interface_abs bd)
        {| abstraction := remapped_abstraction |}.

    Ltac invert_abstraction :=
      match goal with
      | H : remapped_abstraction _ _ |- _ => inversion H; clear H; subst_var; simpl in *
      end.

    Definition rd : Interface RemappedDisk.API.
      unshelve econstructor.
      - exact impl.
      - exact abstr.
      - destruct op.

        + lift_world.
          prog_spec_symbolic_execute inv_step.

          * solve_final_state.
            invert_abstraction.

            (* Prove that the read returns the correct result, by relying on facts
             * from your abstraction. *)
            all: pocs_admit.

          * solve_final_state.
            invert_abstraction.
            exfalso.
            apply disk_inbounds_not_none with (d := d) (a := size d - 1).
            omega.
            auto.

          * solve_final_state.
            invert_abstraction.
            right.
            apply disk_oob_eq.
            omega.

          * solve_final_state.
            invert_abstraction.

            (* Prove that the read returns the correct result, by relying on facts
             * from your abstraction. *)
            all: pocs_admit.

          * solve_final_state.
            invert_abstraction.
            right.
            apply disk_oob_eq.
            apply disk_none_oob in H7. omega.

          * solve_final_state.
            exfalso.
            congruence.

        + (* Prove that your implementation of write creates a state in which your
           * abstraction holds.
           *)
          all: pocs_admit.

        + lift_world.
          prog_spec_symbolic_execute inv_step.
          solve_final_state.
          invert_abstraction.
          omega.

      - cannot_crash.
      - eapply then_init_compose; eauto.
        prog_spec_symbolic_execute inv_step.

        + solve_final_state.
        + match_abstraction_for_step.
          case_eq (d (size d - 1)); intros.
          * exists (diskUpd (shrink d) v1 b); split; [ | constructor ].

            constructor; simpl; autorewrite with upd; auto; intros; destruct_ands; try omega.

            (* Prove that the init function establishes the abstraction.
             *)
            all: pocs_admit.

          * apply disk_none_oob in H. omega.

        + eexists; intuition auto; eauto.

      Grab Existential Variables.
      all: eauto.

    Defined.

  End Implementation.

End RemappedDisk.

Print Assumptions RemappedDisk.rd.
