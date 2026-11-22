/-!
# Glivenko's theorem for propositional logic

A syntactic Hilbert calculus with arbitrary assumptions. Classical logic extends
intuitionistic logic by excluded middle. Negation abbreviates implication to bottom.
No semantic completeness theorem or classical metatheory is needed.
-/

namespace Glivenko

/-- Propositional formulas, with natural numbers as variable names. -/
inductive Formula where
  | atom : Nat → Formula
  | bot : Formula
  | imp : Formula → Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  deriving DecidableEq, Repr

infixr:60 " ⇒ " => Formula.imp
infixr:65 " ⋏ " => Formula.conj
infixr:64 " ⋎ " => Formula.disj
prefix:70 "∼" => fun A => Formula.imp A Formula.bot

/-- The standard intuitionistic Hilbert axiom schemata. -/
inductive IntAxiom : Formula → Prop where
  | k : IntAxiom (A ⇒ B ⇒ A)
  | s : IntAxiom ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
  | explosion : IntAxiom (Formula.bot ⇒ A)
  | conjIntro : IntAxiom (A ⇒ B ⇒ (A ⋏ B))
  | conjLeft : IntAxiom ((A ⋏ B) ⇒ A)
  | conjRight : IntAxiom ((A ⋏ B) ⇒ B)
  | disjLeft : IntAxiom (A ⇒ (A ⋎ B))
  | disjRight : IntAxiom (B ⇒ (A ⋎ B))
  | disjElim : IntAxiom ((A ⇒ C) ⇒ (B ⇒ C) ⇒ (A ⋎ B) ⇒ C)

inductive Logic where
  | intuitionistic
  | classical

/-- Derivability from a list of assumptions; `mp` is modus ponens. -/
inductive Derives (L : Logic) (Γ : List Formula) : Formula → Prop where
  | hyp : A ∈ Γ → Derives L Γ A
  | ax : IntAxiom A → Derives L Γ A
  | mp : Derives L Γ (A ⇒ B) → Derives L Γ A → Derives L Γ B
  | em : L = .classical → Derives L Γ (A ⋎ ∼A)

abbrev IPC := Derives .intuitionistic
abbrev CPC := Derives .classical

namespace Derives

variable {L : Logic} {Γ Δ : List Formula} {A B C : Formula}

/-- A derivation remains valid after adding assumptions. -/
theorem weaken (h : Derives L Γ A) (inc : ∀ X, X ∈ Γ → X ∈ Δ) :
    Derives L Δ A := by
  induction h with
  | hyp hm => exact .hyp (inc _ hm)
  | ax ha => exact .ax ha
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂
  | em he => exact .em he

theorem identity : Derives L Γ (A ⇒ A) :=
  .mp (.mp (.ax .s) (.ax (IntAxiom.k (A := A) (B := A ⇒ A)))) (.ax .k)

/-- The deduction theorem, providing implication introduction as a derived rule. -/
theorem discharge (h : Derives L (A :: Γ) B) : Derives L Γ (A ⇒ B) := by
  induction h with
  | hyp hm =>
    cases hm with
    | head => exact identity
    | tail _ hm => exact .mp (.ax .k) (.hyp hm)
  | ax ha => exact .mp (.ax .k) (.ax ha)
  | mp _ _ ih₁ ih₂ => exact .mp (.mp (.ax .s) ih₁) ih₂
  | em he => exact .mp (.ax .k) (.em he)

theorem lift (h : Derives L Γ A) : Derives L (B :: Γ) A :=
  h.weaken (fun _ hm => List.Mem.tail _ hm)

theorem here : Derives L (A :: Γ) A := .hyp (List.Mem.head _)

theorem doubleNegIntro (h : Derives L Γ A) : Derives L Γ (∼∼A) :=
  discharge (.mp here h.lift)

/-- Double-negated formulas are closed under modus ponens. -/
theorem doubleNegMP (hf : IPC Γ (∼∼(A ⇒ B))) (ha : IPC Γ (∼∼A)) :
    IPC Γ (∼∼B) := by
  apply discharge
  have hnB : IPC (∼B :: Γ) (∼B) := here
  have hnF : IPC (∼B :: Γ) (∼(A ⇒ B)) := by
    apply discharge
    have hnA : IPC ((A ⇒ B) :: ∼B :: Γ) (∼A) := by
      apply discharge
      exact .mp hnB.lift.lift (.mp here.lift here)
    exact .mp ha.lift.lift hnA
  exact .mp hf.lift hnF

/-- Excluded middle itself need not hold in IPC, but its double negation does. -/
theorem doubleNegEM : IPC Γ (∼∼(A ⋎ ∼A)) := by
  apply discharge
  have hn : IPC (∼(A ⋎ ∼A) :: Γ) (∼(A ⋎ ∼A)) := here
  have hnA : IPC (∼(A ⋎ ∼A) :: Γ) (∼A) := by
    apply discharge
    exact .mp hn.lift (.mp (.ax .disjLeft) here)
  exact .mp hn (.mp (.ax .disjRight) hnA)

/-- Every intuitionistic derivation is also a classical derivation. -/
theorem toClassical (h : IPC Γ A) : CPC Γ A := by
  induction h with
  | hyp hm => exact .hyp hm
  | ax ha => exact .ax ha
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂
  | em he => cases he

/-- Classical double-negation elimination, derived from excluded middle. -/
theorem doubleNegElim (h : CPC Γ (∼∼A)) : CPC Γ A := by
  have hn : CPC Γ (∼A ⇒ A) :=
    discharge (.mp (.ax .explosion) (.mp h.lift here))
  exact .mp (.mp (.mp (.ax .disjElim) identity) hn) (.em rfl)

end Derives

/-- Glivenko's theorem, strengthened to an arbitrary unchanged context. -/
theorem glivenko {Γ : List Formula} {A : Formula} (h : CPC Γ A) :
    IPC Γ (∼∼A) := by
  induction h with
  | hyp hm => exact Derives.doubleNegIntro (.hyp hm)
  | ax ha => exact Derives.doubleNegIntro (.ax ha)
  | mp _ _ ih₁ ih₂ => exact Derives.doubleNegMP ih₁ ih₂
  | em _ => exact Derives.doubleNegEM

/-- The usual equivalence, also valid in the presence of assumptions. -/
theorem glivenko_iff {Γ : List Formula} {A : Formula} :
    CPC Γ A ↔ IPC Γ (∼∼A) :=
  ⟨glivenko, fun h => h.toClassical.doubleNegElim⟩

/-- The assumption-free formulation of Glivenko's theorem. -/
theorem glivenko_closed (A : Formula) : CPC [] A ↔ IPC [] (∼∼A) :=
  glivenko_iff

-- These commands let Lean report the metatheoretic axioms used by the proofs.
#print axioms glivenko
#print axioms glivenko_iff
#print axioms glivenko_closed

end Glivenko
