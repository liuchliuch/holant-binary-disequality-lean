import Holant.Complexity.BinaryInterpolation.Chains.Projective
import Holant.Complexity.FixedGadgetSubstitution.TemplateCorrespondence

/-! A literal ordinary replacement template for every positive binary chain.
Every vertex carries the original B label and every internal edge the native
X label. The exact interface keeps the stored ordered boundary and all counts.
It is a semantic compiler interface, not a claim of polynomial bit runtime.
-/
namespace Holant.Complexity.BinaryInterpolation.Chains
open Holant.Certificates.MatchingContractionClosure
open Holant.Complexity.FixedGadgetSubstitution
variable {K : Type*} [Field K]
set_option backward.isDefEq.respectTransparency false

theorem literal_signature (B : Binary (K := K)) (k : ℕ)
    (v : Fin (literal B k).shape.vertices) :
    (⟨(literal B k).shape.arity v, (literal B k).vertex v⟩ : AnySignature K) =
      ⟨2, binarySignature B⟩ :=
  literal_uses B {⟨2, binarySignature B⟩} rfl k v

theorem literal_arity (B : Binary (K := K)) (k : ℕ)
    (v : Fin (literal B k).shape.vertices) : (literal B k).shape.arity v = 2 :=
  congrArg Sigma.fst (literal_signature B k v)

theorem series_shape_independent {J : Type*} [Field J]
    (L R : Network K 2) (L' R' : Network J 2)
    (hL : L.shape = L'.shape) (hR : R.shape = R'.shape) :
    (series L R).shape = (series L' R').shape := by
  rcases L with ⟨SL, vL, eL⟩
  rcases R with ⟨SR, vR, eR⟩
  rcases L' with ⟨SL', vL', eL'⟩
  rcases R' with ⟨SR', vR', eR'⟩
  cases hL
  cases hR
  rfl

/-- Incidence depends only on the positive length, not on a coefficient field
or on any matrix entry. This removes algebraic data from the compiler. -/
theorem literal_shape_independent {J : Type*} [Field J]
    (B : Binary (K := K)) (C : Binary (K := J)) (k : ℕ) :
    (literal B k).shape = (literal C k).shape := by
  induction k with
  | zero => rfl
  | succ k ih => exact series_shape_independent _ _ _ _ ih rfl

/-- A table-free record serializer for a fixed two-port incidence shape. -/
def shapeTemplate (S : NetworkShape 2) (label edge : ℕ) : Template where
  boundary := 2
  vertices := List.ofFn fun v : Fin S.vertices =>
    (label, List.ofFn fun i : Fin (S.arity v) => Labelling.localEndpoint (S.ports ⟨v,i⟩))
  edges := List.replicate S.edges edge

/-- Literal original-family labels on each of the k+1 actual B occurrences. -/
def literalLabelling {s b : ℕ} (arity : ℕ → ℕ)
    (label : Fin s) (hlabel : arity label.val = 2) (edge : Fin b)
    (B : Binary (K := K)) (k : ℕ) : Labelling (literal B k).shape s b arity where
  vertex _ := label
  vertex_arity v := hlabel.trans (literal_arity B k v).symm
  edge _ := edge

/-- Full ordered chain template, suitable for the existing replacement API. -/
def literalTemplate {s b : ℕ} (arity : ℕ → ℕ)
    (label : Fin s) (hlabel : arity label.val = 2) (edge : Fin b)
    (B : Binary (K := K)) (k : ℕ) : Template :=
  (literalLabelling arity label hlabel edge B k).template

theorem literalTemplate_eq_shapeTemplate {s b : ℕ} (arity : ℕ → ℕ)
    (label : Fin s) (hlabel : arity label.val = 2) (edge : Fin b)
    (B : Binary (K := K)) (k : ℕ) :
    literalTemplate arity label hlabel edge B k =
      shapeTemplate (literal B k).shape label.val edge.val := by
  simp [literalTemplate, shapeTemplate, Labelling.template, literalLabelling]

/-- Executable, table-free chain records. The dummy rational zero is used only
to select the already proved incidence shape; it is never an oracle label. -/
def compile (label edge k : ℕ) : Template :=
  shapeTemplate (literal (K := ℚ) 0 k).shape label edge

theorem compile_eq_literalTemplate {s b : ℕ} (arity : ℕ → ℕ)
    (label : Fin s) (hlabel : arity label.val = 2) (edge : Fin b)
    (B : Binary (K := K)) (k : ℕ) :
    compile label.val edge.val k = literalTemplate arity label hlabel edge B k := by
  rw [literalTemplate_eq_shapeTemplate, compile, literal_shape_independent (0 : Binary (K := ℚ)) B k]

@[simp] theorem literalTemplate_boundary {s b : ℕ} (arity : ℕ → ℕ)
    (label : Fin s) (hlabel : arity label.val = 2) (edge : Fin b)
    (B : Binary (K := K)) (k : ℕ) :
    (literalTemplate arity label hlabel edge B k).boundary = 2 := rfl

@[simp] theorem literalTemplate_vertices {s b : ℕ} (arity : ℕ → ℕ)
    (label : Fin s) (hlabel : arity label.val = 2) (edge : Fin b)
    (B : Binary (K := K)) (k : ℕ) :
    (literalTemplate arity label hlabel edge B k).vertices.length = k + 1 := by
  simp [literalTemplate]

@[simp] theorem literalTemplate_edges {s b : ℕ} (arity : ℕ → ℕ)
    (label : Fin s) (hlabel : arity label.val = 2) (edge : Fin b)
    (B : Binary (K := K)) (k : ℕ) :
    (literalTemplate arity label hlabel edge B k).edges.length = k := by
  simp [literalTemplate]

theorem literalTemplate_wellFormed {s b : ℕ} (arity : ℕ → ℕ)
    (label : Fin s) (hlabel : arity label.val = 2) (edge : Fin b)
    (B : Binary (K := K)) (k : ℕ) :
    (literalTemplate arity label hlabel edge B k).WellFormed s b arity :=
  (literalLabelling arity label hlabel edge B k).wellFormed

theorem signature_cast_apply {m n : ℕ} (f : Signature K m) (g : Signature K n)
    (h : (⟨m, f⟩ : AnySignature K) = ⟨n, g⟩) (hmn : m = n)
    (x : Fin n → Bool) : f (fun i => x (Fin.cast hmn i)) = g x := by
  subst n
  have hf : f = g := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  subst g
  rfl

/-- An original binary label and a native edge label give exactly (BX)^(k+1)X.
No analytic pencil coefficient is introduced as a vertex or edge label. -/
theorem literalTemplate_denote {s b : ℕ} (arity : ℕ → ℕ)
    (label : Fin s) (hlabel : arity label.val = 2) (edge : Fin b)
    (B : Binary (K := K)) (k : ℕ)
    (signatures : (i : Fin s) → Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K)
    (hB : (⟨arity label.val, signatures label⟩ : AnySignature K) =
      ⟨2, binarySignature B⟩)
    (hX : kernels edge = Signature.disequality) :
    ((literalTemplate arity label hlabel edge B k).network
      (literalTemplate_wellFormed arity label hlabel edge B k) signatures kernels).denote =
      binarySignature ((B * X) ^ (k + 1) * X) := by
  rw [← literal_denote B k]
  apply Labelling.denote_template_of_labels
  · intro v x
    change signatures label (fun i => x (Fin.cast
      (hlabel.trans (literal_arity B k v).symm) i)) = (literal B k).vertex v x
    apply signature_cast_apply
    exact hB.trans (literal_signature B k v).symm
  · intro e a b
    exact congrFun₂ (hX.trans (literal_native B k e).symm) a b

@[simp] theorem compile_boundary (label edge k : ℕ) : (compile label edge k).boundary = 2 := rfl

@[simp] theorem compile_vertices (label edge k : ℕ) :
    (compile label edge k).vertices.length = k + 1 := by
  simp [compile, shapeTemplate]

@[simp] theorem compile_edges (label edge k : ℕ) :
    (compile label edge k).edges.length = k := by
  simp [compile, shapeTemplate]

theorem compile_wellFormed {s b : ℕ} (arity : ℕ → ℕ)
    (label : Fin s) (hlabel : arity label.val = 2) (edge : Fin b) (k : ℕ) :
    (compile label.val edge.val k).WellFormed s b arity := by
  rw [compile_eq_literalTemplate arity label hlabel edge (0 : Binary (K := ℚ)) k]
  exact literalTemplate_wellFormed arity label hlabel edge 0 k

theorem template_denote_heq {s b : ℕ} {arity : ℕ → ℕ}
    (g h : Template) (hg : g.WellFormed s b arity) (hh : h.WellFormed s b arity)
    (he : g = h) (signatures : (i : Fin s) → Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) :
    HEq (g.network hg signatures kernels).denote (h.network hh signatures kernels).denote := by
  cases he
  rfl

/-- The executable record compiler has the exact source chain denotation. -/
theorem compile_denote {s b : ℕ} (arity : ℕ → ℕ)
    (label : Fin s) (hlabel : arity label.val = 2) (edge : Fin b) (k : ℕ)
    (B : Binary (K := K))
    (signatures : (i : Fin s) → Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K)
    (hB : (⟨arity label.val, signatures label⟩ : AnySignature K) =
      ⟨2, binarySignature B⟩)
    (hX : kernels edge = Signature.disequality) :
    ((compile label.val edge.val k).network
      (compile_wellFormed arity label hlabel edge k) signatures kernels).denote =
      binarySignature ((B * X) ^ (k + 1) * X) := by
  have he := template_denote_heq _ _ (compile_wellFormed arity label hlabel edge k)
    (literalTemplate_wellFormed arity label hlabel edge B k)
    (compile_eq_literalTemplate arity label hlabel edge B k) signatures kernels
  exact (eq_of_heq he).trans
    (literalTemplate_denote arity label hlabel edge B k signatures kernels hB hX)

/-- Scaled original input tables remain scaled in the actual oracle template.
The scalar is c^(k+1), not a new label or a discarded normalization. -/
theorem compile_denote_scaled {s b : ℕ} (arity : ℕ → ℕ)
    (label : Fin s) (hlabel : arity label.val = 2) (edge : Fin b) (k : ℕ)
    (B : Binary (K := K)) (c : K)
    (signatures : (i : Fin s) → Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K)
    (hB : (⟨arity label.val, signatures label⟩ : AnySignature K) =
      ⟨2, c • binarySignature B⟩)
    (hX : kernels edge = Signature.disequality) :
    ((compile label.val edge.val k).network
      (compile_wellFormed arity label hlabel edge k) signatures kernels).denote =
      c ^ (k + 1) • binarySignature ((B * X) ^ (k + 1) * X) := by
  rw [compile_denote arity label hlabel edge k (c • B) signatures kernels hB hX,
    scaled_transfer_power, binarySignature_smul]

end Holant.Complexity.BinaryInterpolation.Chains
