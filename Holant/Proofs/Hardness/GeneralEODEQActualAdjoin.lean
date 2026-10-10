import Holant.Proofs.Hardness.GeneralEODEQPairingSource
import Holant.Proofs.Reductions.ControlledCap

/-! An actual original-labelled projective DEQ4 graph is installed and removed
by the finite scaled-substitution machine. Its scalar remains in the original
fixed field, and the final oracle table and codec are unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQActualAdjoin
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace M
export GeneralEODEQPairingTemplates (family)
end M
namespace R
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end R
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {a : ℕ → ℕ}
variable (F : FixedField K d) (T : ExactSignatureTables d s 1 a)
variable (N : Network K 4) (L : Labelling N.shape s 1 a)
variable (c : K)

abbrev arity := sourceArity (Adjoin.templates s a L.template)
abbrev coordinates := ScaledAdjoin.coordinates F T L.template L.wellFormed c
abbrev tables := sourceTables (Adjoin.templates s a L.template) T (coordinates F T N L c)
abbrev signatures := M.family F (tables F T N L c)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (s+1) 1 (arity N L)
abbrev value := (tables F T N L c).evaluate F

omit [Field K] [Algebra ℚ K] in
private theorem apply_exact {m n : ℕ} (f : Signature K m) (g : Signature K n)
    (eqn : (⟨m,f⟩ : AnySignature K)=⟨n,g⟩) (h : m=n) (x : Fin n → Bool) :
    f (fun i => x (Fin.cast h i))=g x := by
  cases eqn
  rfl

variable (labels : LabelledNetwork.Exact (M.family F T) N L)
variable (native : ∀ j x y, F.decode (T.edge j x y)=Signature.disequality x y)
variable (edges : ∀ j, N.edge j=Signature.disequality)
variable (scaled : N.denote=c • ExactTwoSignatures.E)

include labels native edges scaled in
theorem macro_scaled :
    (L.template.network L.wellFormed (M.family F T)
      (fun j x y => F.decode (T.edge j x y))).denote=c • ExactTwoSignatures.E := by
  calc
    _ = N.denote := by
      apply L.denote_template_of_labels
      · intro v x
        exact apply_exact _ _ (labels v) (L.vertex_arity v) x
      · intro j x y
        change Fin N.shape.edges at j
        change F.decode (T.edge (L.edge j) x y)=N.edge j x y
        rw [native,edges]
    _ = _ := scaled

private def decodeAny (z : AnySignature (Fin d → ℚ)) : AnySignature K :=
  ⟨z.1,fun x => F.decode (z.2 x)⟩

theorem old_signature (i : Fin s) :
    (⟨arity N L i.val,signatures F T N L c ⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩⟩ :
      AnySignature K)=⟨a i.val,M.family F T i⟩ := by
  have h : (⟨arity N L i.val,
      coordinates F T N L c ⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩⟩ :
        AnySignature (Fin d → ℚ))=⟨a i.val,T.vertex i⟩ :=
    Sigma.ext (Adjoin.old_boundary L.template i)
      (ScaledAdjoin.old_coordinates F T L.template L.wellFormed c i)
  exact congrArg (decodeAny F) h

include labels native edges scaled in
theorem new_signature (hc : c≠0) :
    (⟨arity N L s,signatures F T N L c ⟨s,Nat.lt_succ_self s⟩⟩ : AnySignature K)=
      ⟨4,ExactTwoSignatures.E⟩ := by
  have h : (⟨arity N L s,coordinates F T N L c ⟨s,Nat.lt_succ_self s⟩⟩ :
      AnySignature (Fin d → ℚ))=⟨4,fun x => F.decode.symm
        ((L.template.network L.wellFormed (M.family F T)
          (fun j x y => F.decode (T.edge j x y))).denote x/c)⟩ :=
    Sigma.ext (Adjoin.new_boundary L.template)
      (ScaledAdjoin.new_coordinates F T L.template L.wellFormed c)
  refine (congrArg (decodeAny F) h).trans ?_
  change (⟨4,fun x => F.decode (F.decode.symm
    ((L.template.network L.wellFormed (M.family F T)
      (fun j x y => F.decode (T.edge j x y))).denote x/c))⟩ : AnySignature K)=_
  congr 1
  funext x
  rw [LinearEquiv.apply_symm_apply,macro_scaled F T N L c labels native edges scaled]
  exact mul_div_cancel_left₀ (ExactTwoSignatures.E x) hc

include native in
theorem native_tables : ∀ j x y,
    F.decode ((tables F T N L c).edge j x y)=Signature.disequality x y := native

/-- Each E occurrence is replaced by the actual supplied graph, and its
nonzero scalar is removed to the actual number of occurrences. -/
def remove (hc : c≠0) : LengthControlledOracleReduction (inputEncoding N L) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding (value F T N L c) (T.evaluate F) :=
  Holant.LocalDrafts.Hardness.ControlledCap.scaledAdjoin F T L.template L.wellFormed c hc

/-- Every chosen pairing can now be imposed physically before ordinary CSP
occurrence cycles are compiled; the last oracle has only the original rows. -/
def pairingSource (hc : c≠0)
    (P : (i : Fin (s+1)) → OrientedPerfectPairing (arity N L i.val)) :
    LengthControlledOracleReduction (GeneralEOPairedCSPFamilyRaw.encoding (s+1)) F.encoding
      (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
      (GeneralEOPairedCSPFamilyNative.totalValue (signatures F T N L c) P) (T.evaluate F) :=
  R.composeControlled
    (GeneralEODEQPairingSource.controlled F (tables F T N L c) P ⟨s,Nat.lt_succ_self s⟩
      (new_signature F T N L c labels native edges scaled hc)
      (native_tables F T N L c native))
    (remove F T N L c hc)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQActualAdjoin
