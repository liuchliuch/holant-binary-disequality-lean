import Holant.Complexity.EdgeSubdivision.WirePath
import Holant.Complexity.EdgeSubdivision.VertexSubstitution

/-! Remove the old extra wire signature by a two-vertex path, preserving every
original family label and using the new literal wire signature as a resource. -/
namespace Holant.Complexity.EdgeSubdivision.WireMacros
open FixedGadgetSubstitution
noncomputable section
set_option backward.isDefEq.respectTransparency false

def middleArity (s : ℕ) (arity : ℕ → ℕ) := targetArity (s+1) (targetArity s arity)

def templates (s : ℕ) (arity : ℕ → ℕ) (i : ℕ) : Template :=
  if i<s then identityTemplate (targetArity s arity) i
  else if i=s then WirePath.template s arity
  else identityTemplate (targetArity s arity) s

theorem boundary (s : ℕ) (arity : ℕ → ℕ) :
    sourceArity (templates s arity)=middleArity s arity := by
  funext i
  by_cases hi : i<s
  · simp [sourceArity,templates,hi,identityTemplate,middleArity,targetArity,show i<s+1 by omega]
  · by_cases he : i=s
    · subst i
      simp [sourceArity,templates,WirePath.boundary,middleArity,targetArity]
    · have hh : ¬i<s+1 := by omega
      simp [sourceArity,templates,hi,he,identityTemplate,middleArity,targetArity,hh]

theorem valid (s : ℕ) (arity : ℕ → ℕ) : ∀ i<s+2,
    (templates s arity i).WellFormed (s+1) 1 (targetArity s arity) := by
  intro i hi
  by_cases hs : i<s
  · simpa only [templates,if_pos hs] using
      identityTemplate_wellFormed (b:=1) (targetArity s arity)
        (⟨i,by omega⟩ : Fin (s+1))
  · by_cases he : i=s
    · subst i
      simpa [templates] using WirePath.valid s arity
    · simpa [templates,hs,he] using
        identityTemplate_wellFormed (b:=1) (targetArity s arity) (⟨s,Nat.lt_succ_self s⟩ : Fin (s+1))

variable {K : Type} [CommSemiring K] {s : ℕ} {arity : ℕ → ℕ}
variable (source : (i : Fin s) → Signature K (arity i.val))

def middleSignatures (p q : Bool) :
    (i : Fin ((s+1)+1)) → Signature K (middleArity s arity i.val) :=
  extendedSignatures (extendedSignatures source (fun _ : Fin 1 => WirePath.kernel p))
    (fun _ : Fin 1 => WirePath.kernel q)

theorem network_value_congr {a c : Template} (he : a=c)
    (ha : a.WellFormed (s+1) 1 (targetArity s arity))
    (hc : c.WellFormed (s+1) 1 (targetArity s arity))
    (sig : (i : Fin (s+1)) → Signature K (targetArity s arity i.val))
    (wire : Fin 1 → Bool → Bool → K) (x : Fin a.boundary → Bool) :
    (a.network ha sig wire).denote x =
      (c.network hc sig wire).denote
        (fun j => x (Fin.cast (congrArg Template.boundary he).symm j)) := by
  cases he
  rfl

theorem macro_value (p q : Bool) (i : Fin (s+2))
    (x : Fin ((templates s arity i.val).boundary) → Bool) :
    ((templates s arity i.val).network (valid s arity i.val i.isLt)
      (extendedSignatures source (fun _ : Fin 1 => WirePath.kernel q))
      (fun _ : Fin 1 => WirePath.kernel p)).denote x =
      middleSignatures source p q i
        (fun j => x (Fin.cast (congrFun (boundary s arity) i.val).symm j)) := by
  by_cases hi : i.val<s
  · have hi' : i.val<s+1 := by omega
    have ht : templates s arity i.val = identityTemplate (targetArity s arity) i.val := by
      simp [templates,hi]
    have h := network_value_congr ht (valid s arity i.val i.isLt)
      (identityTemplate_wellFormed (b:=1) (targetArity s arity) (⟨i.val,hi'⟩ : Fin (s+1)))
      (extendedSignatures source (fun _ : Fin 1 => WirePath.kernel q))
      (fun _ : Fin 1 => WirePath.kernel p) x
    rw [identityTemplate_denote (targetArity s arity) (⟨i.val,hi'⟩ : Fin (s+1))
      (extendedSignatures source (fun _ : Fin 1 => WirePath.kernel q))
      (fun _ : Fin 1 => WirePath.kernel p)] at h
    simpa [middleSignatures,extendedSignatures,hi,hi'] using h
  · by_cases he : i.val=s
    · have ht : templates s arity i.val = WirePath.template s arity := by simp [templates,hi,he]
      have h := network_value_congr ht (valid s arity i.val i.isLt)
        (WirePath.valid s arity)
        (extendedSignatures source (fun _ : Fin 1 => WirePath.kernel q))
        (fun _ : Fin 1 => WirePath.kernel p) x
      rw [WirePath.template_denote] at h
      simpa [middleSignatures,extendedSignatures,he] using h
    · have hi' : i.val=s+1 := by have hib := i.isLt; omega
      have ht : templates s arity i.val = identityTemplate (targetArity s arity) s := by
        simp [templates,hi,he]
      have h := network_value_congr ht (valid s arity i.val i.isLt)
        (identityTemplate_wellFormed (b:=1) (targetArity s arity) (⟨s,Nat.lt_succ_self s⟩ : Fin (s+1)))
        (extendedSignatures source (fun _ : Fin 1 => WirePath.kernel q))
        (fun _ : Fin 1 => WirePath.kernel p) x
      rw [identityTemplate_denote (targetArity s arity) (⟨s,Nat.lt_succ_self s⟩ : Fin (s+1))
        (extendedSignatures source (fun _ : Fin 1 => WirePath.kernel q))
        (fun _ : Fin 1 => WirePath.kernel p)] at h
      simpa [middleSignatures,extendedSignatures,hi'] using h

end
end Holant.Complexity.EdgeSubdivision.WireMacros
