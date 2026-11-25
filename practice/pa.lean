section NatAdd

open Nat

theorem nat_ind: forall P: Nat -> Prop,
  P 0 -> (forall n, P n -> P (Nat.succ n)) -> forall n, P n := by
    apply Nat.recAux

theorem succ_add: forall a b: Nat, a.succ + b = (a + b).succ
  | _, 0 => rfl
  | n, succ m => by
    rw [add_succ]
    rw [add_succ]
    rw [succ_add n]

theorem nat_comm: forall a: Nat, forall b: Nat, a + b = b + a := by
  intro a
  induction a with
  | zero => simp
  | succ a H => {
      intro b
      rw [add_succ b a]
      rw [<- H b]
      apply _root_.succ_add
  }

theorem nat_assoc: forall a b c: Nat, a + b + c = a + (b + c) := by
  intros a b c
  induction c with
  | zero => simp
  | succ c H => {
    rw [add_succ]
    rw [add_succ]
    rw [add_succ]
    rw [H]
  }

end NatAdd
