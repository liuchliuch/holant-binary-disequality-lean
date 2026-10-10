import Holant.Proofs.Traversal.ArityTwo.SelectedProvider


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.RawCompiler
open Holant Holant.Complexity Computability Holant.OneHot.StackProgram
open BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open Holant.OneHot.StackProgram.GraphLabelEncoding PortWalk Descriptors
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (s b : ℕ) (arity : ℕ → ℕ) {A : Type}
variable (labels : (i : Fin s) → Signature A (arity i.val))
variable (edges : Fin b → Kernel A) (codec : Encoding A Bool)
variable (hd : ∀ i : Fin s, arity i.val ≤ 2)

abbrev Input := FixedGadgetSubstitution.Compiler.Input s b arity
abbrev encoding := RawClosedNetwork.validatedEncoding s b arity
abbrev Index (r : Input s b arity) := {v : Fin r.val.vertices.length // (r.val.graph r.property).label v = v}
def indexEncoding (r : Input s b arity) :=
  RunComposition.restricted (OccurrenceLabel.unaryPortEncoding r.val.vertices.length)
    (fun v => (r.val.graph r.property).label v = v)

def roots (r : Input s b arity) : List (Index s b arity r) :=
  List.ofFn (fun i : Fin (r.val.graph r.property).roots.length =>
    ⟨(r.val.graph r.property).roots.get i,
      ((r.val.graph r.property).mem_roots _).mp (List.get_mem _ i)⟩)

theorem roots_original (r : Input s b arity) :
    (roots s b arity r).map Subtype.val = (r.val.graph r.property).roots := by
  simp only [roots,List.map_ofFn]
  exact List.ofFn_get _

theorem roots_word (r : Input s b arity) :
    ComponentSelection.RawRoots.outputEncoding.encode (ComponentSelection.RawRoots.value r) =
      framedListEncode (indexEncoding s b arity r) (roots s b arity r) := by
  have aux (vs : List (Index s b arity r)) :
      framedListEncode UnaryBinary.unaryEncoding (vs.map (fun v => v.val.val)) =
        framedListEncode (indexEncoding s b arity r) vs := by
    induction vs with
    | nil => rfl
    | cons v vs ih => simp only [List.map_cons,framedListEncode,ih]; rfl
  have h := aux (roots s b arity r)
  change framedListEncode UnaryBinary.unaryEncoding
    ((r.val.graph r.property).roots.map Fin.val) = _
  rw [← roots_original s b arity r, List.map_map]
  exact h

def contextEncoding := ContextFlatMap.inputEncoding (encoding s b arity) (indexEncoding s b arity)
def prepareComputes : Computes (encoding s b arity) (contextEncoding s b arity)
    (fun r => ⟨r,roots s b arity r⟩) :=
  recode (RawBytecodeMachine.rootsComputes s b arity) id (fun _ => rfl)
    (fun r => by
      change Holant.Algebraic.frame _ ++ _ = Holant.Algebraic.frame _ ++ _
      rw [roots_word]
      rfl)

abbrev Query := Σ r : Input s b arity, Index s b arity r
def queryEncoding := sigmaEncoding (encoding s b arity) (indexEncoding s b arity)
def rootQuery (x : Query s b arity) : SelectedProvider.Root s b arity :=
  ⟨⟨x.1,x.2.val⟩,x.2.property⟩
def chunk (x : Query s b arity) := SelectedProvider.rootValue s b arity labels edges codec (rootQuery s b arity x)

def chunkComputes : Computes (queryEncoding s b arity) Frame.wordEncoding (chunk s b arity labels edges codec) :=
  recode (SelectedProvider.rootComputes s b arity labels edges codec hd)
    (rootQuery s b arity) (fun _ => rfl) (fun _ => rfl)

def chunks (r : Input s b arity) :=
  (roots s b arity r).flatMap (fun v => chunk s b arity labels edges codec ⟨r,v⟩)
def chunksComputes : Computes (encoding s b arity) Frame.wordEncoding (chunks s b arity labels edges codec) :=
  (prepareComputes s b arity).andThen
    (ContextFlatMap.computes (encoding s b arity) (indexEncoding s b arity)
      (chunk s b arity labels edges codec) (chunkComputes s b arity labels edges codec hd))

def multiplies (r : Input s b arity) :=
  (roots s b arity r).flatMap (fun _ => MatrixEmission.word codec [.mul])
def multiplyComputes : Computes (encoding s b arity) Frame.wordEncoding (multiplies s b arity codec) :=
  (prepareComputes s b arity).andThen
    (ContextFlatMap.computes (encoding s b arity) (indexEncoding s b arity)
      (fun _ => MatrixEmission.word codec [.mul])
      (constantComputes (queryEncoding s b arity) Frame.wordEncoding (MatrixEmission.word codec [.mul])))

def emitted (r : Input s b arity) :=
  chunks s b arity labels edges codec r ++
    (MatrixEmission.word codec [.one] ++ multiplies s b arity codec r) ++ [false]
def wordComputes : Computes (encoding s b arity) Frame.wordEncoding (emitted s b arity labels edges codec) :=
  joinComputes (joinComputes (chunksComputes s b arity labels edges codec hd)
    (joinComputes (constantComputes (encoding s b arity) Frame.wordEncoding (MatrixEmission.word codec [.one]))
      (multiplyComputes s b arity codec)))
    (constantComputes (encoding s b arity) Frame.wordEncoding [false])

def vertex (r : Input s b arity) := ActionTableMeaning.vertex r.val r.property labels
def edge (r : Input s b arity) := ActionTableMeaning.edge r.val r.property edges
def descriptors (r : Input s b arity) := (all r.val r.property (vertex s b arity labels r) (edge s b arity edges r)).getD []
def code (r : Input s b arity) := componentsCode (descriptors s b arity labels edges r)

include hd in
theorem chunks_original (r : Input s b arity) (cs : List (Component A))
    (hc : all r.val r.property (vertex s b arity labels r) (edge s b arity edges r) = some cs) :
    chunks s b arity labels edges codec r = cs.flatMap (fun c => MatrixEmission.word codec c.code) ∧
      (roots s b arity r).length = cs.length := by
  have aux (vs : List (Index s b arity r)) (cs : List (Component A))
      (hc : (vs.map Subtype.val).mapM (component r.val r.property (vertex s b arity labels r) (edge s b arity edges r)) = some cs) :
      vs.flatMap (fun v => chunk s b arity labels edges codec ⟨r,v⟩) =
        cs.flatMap (fun c => MatrixEmission.word codec c.code) ∧ vs.length = cs.length := by
    induction vs generalizing cs with
    | nil => have he : cs = [] := by simpa using hc.symm
             subst cs
             exact ⟨rfl,rfl⟩
    | cons v vs ih =>
      obtain ⟨c,hc₀,hw⟩ := SelectedProvider.rootValue_original s b arity labels edges codec hd (rootQuery s b arity ⟨r,v⟩)
      change component r.val r.property (vertex s b arity labels r) (edge s b arity edges r) v.val = some c at hc₀
      cases ht : (vs.map Subtype.val).mapM (component r.val r.property (vertex s b arity labels r) (edge s b arity edges r)) with
      | none => simp only [List.map_cons,List.mapM_cons, hc₀,ht,Option.bind_some,Option.bind_none] at hc
                cases hc
      | some ds =>
        have he : cs = c::ds := by simpa only [List.map_cons,List.mapM_cons,hc₀,ht,bind,Option.bind_some,Option.pure_def,Option.some.injEq] using hc.symm
        subst cs
        obtain ⟨hh,hl⟩ := ih ds ht
        constructor
        · simp only [List.flatMap_cons,hh]
          exact congrArg (fun tail => tail ++ ds.flatMap (fun d => MatrixEmission.word codec d.code)) hw
        · simp [hl]
  apply aux
  simpa only [roots_original,all] using hc

theorem multiplies_word (r : Input s b arity) : multiplies s b arity codec r =
    MatrixEmission.word codec (List.replicate (roots s b arity r).length Op.mul) := by
  unfold multiplies
  induction roots s b arity r with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.flatMap_cons,List.length_cons,List.replicate_succ,ih]
    simp only [MatrixEmission.word,entries,List.flatMap_cons,List.flatMap_nil,List.append_nil]

include hd in
theorem emitted_original (r : Input s b arity) : emitted s b arity labels edges codec r =
    (codeEncoding codec).encode (code s b arity labels edges r) := by
  obtain ⟨cs,hc⟩ := all_total r.val r.property (vertex s b arity labels r) (edge s b arity edges r)
    (fun v => hd (r.val.signatureLabel r.property v))
  obtain ⟨hh,hl⟩ := chunks_original s b arity labels edges codec hd r cs hc
  have hword := entries_append_encode (opEncoding codec) (componentsCode cs) []
  rw [RawBytecodeMachine.componentsCode_flat] at hword
  simpa [emitted,hh,multiplies_word,hl,code,descriptors,hc,MatrixEmission.word,entries,
    RawBytecodeMachine.componentsCode_flat,List.flatMap_append,List.flatMap_assoc,List.append_assoc,codeEncoding,framedListEncoding,framedListEncode] using hword

/-- A genuine raw-input compiler witness: scanning and emission are charged by
the composed real-machine polynomials, including the empty graph's output. -/
def computes : Computes (encoding s b arity) (codeEncoding codec) (code s b arity labels edges) :=
  recode (wordComputes s b arity labels edges codec hd) id (fun _ => rfl)
    (emitted_original s b arity labels edges codec hd)

theorem computes_machine : (computes s b arity labels edges codec hd).machine =
    RawBytecodeMachine.compiler s b arity labels edges codec := by
  simp only [computes,recode,wordComputes,chunksComputes,multiplyComputes,
    RunComposition.andThen_machine,joinComputes,pairComputes_machine,
    prepareComputes,recode,ContextFlatMap.computes,chunkComputes,
    SelectedProvider.rootComputes_machine,constantComputes,Frame.wordEncoding,id_eq,
    RawBytecodeMachine.compiler,RawBytecodeMachine.join,WordJoin.computes]

include hd in
theorem inFP : InFP (encoding s b arity) (codeEncoding codec) (code s b arity labels edges) :=
  (computes s b arity labels edges codec hd).inFP

theorem primitive_bound (r : Input s b arity) :
    let w := computes s b arity labels edges codec hd
    primitiveCost w.machine (w.outputs r).steps
      (some (Turing.initList w.machine.computer (RawClosedNetwork.encoding.encode r.val))) ≤
        (primitivePolynomial w).eval (RawClosedNetwork.encoding.encode r.val).length :=
  computes_primitive_cost (computes s b arity labels edges codec hd) r

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.RawCompiler
