import Holant.Proofs.BinaryInterpolation.PhysicalQueries
import Holant.Complexity.BinaryInterpolation.AlgebraicSource.Macro


namespace Holant.LocalDrafts.BinaryInterpolation.OriginalTables
open Holant.Complexity Holant.Complexity.BinaryInterpolation
open Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.BinaryInterpolation.Chains
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
variable {K : Type} [Field K] {s b : ℕ} {arity : ℕ → ℕ}

def castSignature {a n : ℕ} (h : a = n) (f : Signature K a) : Signature K n := h ▸ f

theorem castSignature_any {a n : ℕ} (h : a = n) (f : Signature K a) :
    (⟨n, castSignature h f⟩ : AnySignature K) = ⟨a, f⟩ := by
  subst n
  rfl

variable (g : Template) (hg : g.WellFormed s b arity)
variable (G : (i : Fin s) → Signature K (arity i.val))
variable (kernels : Fin b → Bool → Bool → K)

/-- These are the original Γ corollas plus the exact physical macro table.
This is fixed coefficient data, not input-dependent oracle advice. -/
def tables (i : Fin (s+1)) :
    Signature K (PhysicalQueries.A (s:=s) arity g i.val) :=
  ((Adjoin.templates s arity g i.val).network (Adjoin.wellFormed g hg i.val i.isLt)
    G kernels).denote

theorem tables_local (i : Fin (s+1)) :
    ((Adjoin.templates s arity g i.val).network (Adjoin.wellFormed g hg i.val i.isLt)
      G kernels).denote =
      (if i.val = s then (1:K) else 1) • tables g hg G kernels i := by
  simp [tables]

theorem tables_new :
    (⟨PhysicalQueries.A (s:=s) arity g s,
      tables g hg G kernels PhysicalQueries.newLabel⟩ : AnySignature K) =
      ⟨g.boundary, (g.network hg G kernels).denote⟩ := by
  exact PhysicalQueries.templateSignature_eq _ _ _ hg
    (by simp [Adjoin.templates]) G kernels

theorem tables_old (i : Fin s) :
    (⟨PhysicalQueries.A (s:=s) arity g i.val,
      tables g hg G kernels ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩⟩ : AnySignature K) =
      ⟨arity i.val, G i⟩ := by
  have ht := PhysicalQueries.templateSignature_eq
    (Adjoin.templates s arity g i.val) (identityTemplate arity i.val)
    (Adjoin.wellFormed g hg i.val (Nat.lt_trans i.isLt (Nat.lt_succ_self s)))
    (identityTemplate_wellFormed arity i) (by simp [Adjoin.templates, i.isLt]) G kernels
  apply ht.trans
  rw [identityTemplate_denote arity i G kernels]
  rfl

variable (hbinary : g.boundary = 2)

/-- Change only the new slot, preserving its ordered two ports by transport.
Every old entry remains the actual original corolla table. -/
def binarySlot (B : Binary (K:=K)) (i : Fin (s+1)) :
    Signature K (PhysicalQueries.A (s:=s) arity g i.val) :=
  if hi : i.val = s then
    castSignature ((congrArg (PhysicalQueries.A (s:=s) arity g) hi).trans
      (PhysicalQueries.new_arity arity g hbinary)).symm (binarySignature B)
  else tables g hg G kernels i

theorem binarySlot_new (B : Binary (K:=K)) :
    (⟨PhysicalQueries.A (s:=s) arity g s,
      binarySlot g hg G kernels hbinary B PhysicalQueries.newLabel⟩ : AnySignature K) =
      ⟨2, binarySignature B⟩ := by
  simp only [binarySlot, PhysicalQueries.newLabel, dif_pos rfl]
  exact castSignature_any _ _

theorem binarySlot_old (B : Binary (K:=K)) (i : Fin s) :
    (⟨PhysicalQueries.A (s:=s) arity g i.val,
      binarySlot g hg G kernels hbinary B
        ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩⟩ : AnySignature K) =
      ⟨arity i.val, G i⟩ := by
  have hi : i.val ≠ s := Nat.ne_of_lt i.isLt
  simpa only [binarySlot, dif_neg hi] using tables_old g hg G kernels i

theorem right_eq_binarySlot (B : Binary (K:=K)) :
    RawPolynomial.right (tables g hg G kernels)
      (binarySlot g hg G kernels hbinary B) s = binarySlot g hg G kernels hbinary B := by
  funext i x
  by_cases hi : i.val = s
  · simp [RawPolynomial.right, hi]
  · simp [RawPolynomial.right, binarySlot, hi]

end

noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature ℂ (arity i.val))
variable {B : Binary (K:=ℂ)} (M : AlgebraicSource.Macro G B)
variable (p : AlgebraicSource.Pencil M.binary)

/-- A closed-query recovery theorem with no caller-supplied local semantics:
Macro and Pencil are constructed from source realizability and infinite order
by the existing algebraic-source theorems. -/
theorem macro_recovery
    (r : PhysicalQueries.Source (s:=s) (b:=1) arity M.label.template) :
    recoverTop (fun i : Fin (occurrences s r.val+1) => p.node (i.val+1))
      (fun i =>
        ((Compiler.OriginalFamily.value arity M.label.template M.label.wellFormed rfl
          (0 : Fin 1) ⟨r,i⟩).val.realize
          (Compiler.OriginalFamily.value arity M.label.template M.label.wellFormed rfl
            (0 : Fin 1) ⟨r,i⟩).property G
            (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 /
              p.beta^((i.val+1)*occurrences s r.val)) =
    (r.val.realize r.property
      (binarySlot M.label.template M.label.wellFormed G
        (fun _ : Fin 1 => Signature.disequality) rfl p.H)
      (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 := by
  let S := tables M.label.template M.label.wellFormed G
    (fun _ : Fin 1 => Signature.disequality)
  let L := binarySlot M.label.template M.label.wellFormed G
    (fun _ : Fin 1 => Signature.disequality) rfl p.L
  let R := binarySlot M.label.template M.label.wellFormed G
    (fun _ : Fin 1 => Signature.disequality) rfl p.H
  have hB : (⟨PhysicalQueries.A (s:=s) arity M.label.template s,
      S PhysicalQueries.newLabel⟩ : AnySignature ℂ) = ⟨2, binarySignature M.binary⟩ := by
    exact (tables_new M.label.template M.label.wellFormed G
      (fun _ : Fin 1 => Signature.disequality)).trans
        (congrArg (fun f : Signature ℂ 2 => (⟨2,f⟩ : AnySignature ℂ)) M.denote_exact)
  have h := PhysicalQueries.recovery arity M.label.template M.label.wellFormed rfl
    (0 : Fin 1) S L R G (fun _ : Fin 1 => Signature.disequality)
    M.binary p.L p.H p.beta p.node hB
    (binarySlot_new M.label.template M.label.wellFormed G
      (fun _ : Fin 1 => Signature.disequality) rfl p.L)
    (binarySlot_new M.label.template M.label.wellFormed G
      (fun _ : Fin 1 => Signature.disequality) rfl p.H)
    rfl p.power_identity 1
    (tables_local M.label.template M.label.wellFormed G
      (fun _ : Fin 1 => Signature.disequality)) r one_ne_zero p.beta_nonzero
    (p.positive_nodes_injective (occurrences s r.val))
  simp only [one_mul, S, R] at h
  have hr := right_eq_binarySlot (s:=s) (b:=1) (arity:=arity) M.label.template
    M.label.wellFormed G (fun _ : Fin 1 => Signature.disequality) rfl p.H
  rw [hr] at h
  exact h

/-- Select the actual original-family macro and a nonzero rank-one algebraic
pencil from precisely the nonsingular infinite-order source hypotheses. -/
theorem source_data (halg : ∀ i x, IsAlgebraic ℚ (G i x))
    (B : Binary (K:=ℂ)) (hB : B ≠ 0) (hd : Matrix.det (B*X) ≠ 0)
    (hi : ¬ ProjectivelyFinite (B*X))
    (hreal : Gadget.RealizesUpTo
      (Set.range (fun i => (⟨arity i.val, G i⟩ : AnySignature ℂ)))
      .disequality (binarySignature B)) :
    ∃ M : AlgebraicSource.Macro G B, Nonempty (AlgebraicSource.Pencil M.binary) := by
  obtain ⟨M⟩ := AlgebraicSource.exists_macro G halg B hB hd hi hreal
  exact ⟨M, M.pencil_exists⟩

end
end Holant.LocalDrafts.BinaryInterpolation.OriginalTables
