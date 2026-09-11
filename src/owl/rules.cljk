(ns owl.rules
  "RDFS and OWL 2 RL entailment written as DATALOG RULES, for a query engine
  that evaluates recursion to a least fixpoint.

  ## Why this exists next to `owl.reason`

  `owl.reason` computes three closures IN MEMORY, over an `owl.model`
  ontology, in a single non-iterated pass. That is the right shape when you
  hold the whole ontology as a value. It is the wrong shape when the
  ontology is a stored graph too large to hold, because it requires
  materialising every asserted fact before answering anything.

  These rules move the same semantics to the query. They are plain EDN --
  `[[(head ?a ?b) body-clause ...] ...]`, the shape kotobase's `:rules`
  takes -- so the engine runs the fixpoint against its own indexes and only
  the predicates a rule names are ever read. Nothing here evaluates
  anything; this namespace emits rules, exactly as the rest of this library
  emits data.

  ## Two rulesets, and the difference is a full scan

  `hierarchy-rules` names its predicates LITERALLY, so an engine that plans
  reads per predicate touches three ranges. It covers what an ontology is
  usually asked -- transitive `rdfs:subClassOf`, transitive
  `rdfs:subPropertyOf`, and `rdf:type` closed over the class hierarchy
  (RDFS rules 9 and 11, and 5).

  `triple-rules` derives triples whose PREDICATE is a variable --
  `rdfs:subPropertyOf` propagation, `rdfs:domain`/`rdfs:range` typing,
  `owl:TransitiveProperty`, `owl:SymmetricProperty`, `owl:inverseOf`. That
  is strictly more entailment and it costs an unbounded scan: its base case
  is `[?s ?p ?o]`, which no predicate index can narrow. Both are offered
  rather than one merged ruleset because the choice is a cost decision the
  caller has to make with the number in front of them, and a merged ruleset
  would hide it -- the narrow one would silently become the wide one.

  ## What this is not

  Not a description-logic reasoner, for the same reason `owl.reason` is not:
  Datalog is Horn, so it has no disjunction, no existential introduction and
  no cardinality arithmetic. `owl:someValuesFrom`, `owl:unionOf`,
  `owl:maxCardinality`, `owl:disjointWith` consistency checking and anything
  else that needs to reason about models rather than derive facts are OUT,
  and adding them here is not a matter of writing more rules. This is the
  OWL 2 RL / RDFS fragment: the part of OWL whose entailment IS a fixpoint
  over Horn clauses, which is the part production triple stores implement
  and the part that is worth having.

  Also out, deliberately: `owl:sameAs`. Its rules are sound -- replace a
  term by an equal one anywhere -- and they multiply the derived set by the
  square of each equivalence class while making every answer ambiguous
  about which name it came back under. A caller that wants it should say
  so, in its own rules, having decided that.

  ## Vocabulary

  A rule can only match the term a graph actually stored. Two conventions
  are supported and neither is guessed: `keyword-vocabulary` (the natural
  form when the writer used Clojure keywords, which is what kotobase's
  write path stringifies) and `iri-vocabulary` (full W3C IRIs, the form an
  RDF import produces). Pass your own map to match anything else -- the
  keys are this namespace's, the values are yours.

      (require '[owl.rules :as rules])

      (rules/hierarchy-rules)                    ;; keyword vocabulary
      (rules/triple-rules rules/iri-vocabulary)  ;; imported RDF

      ;; every class Felix belongs to, however deep the hierarchy
      {:find  '[?class]
       :where '[(owl-type \"Felix\" ?class)]
       :rules (rules/hierarchy-rules)}")

(def keyword-vocabulary
  "RDFS/OWL terms as Clojure keywords -- the form a graph written natively
  in this stack holds. `:rdf/type` rather than the IRI it abbreviates."
  {:type                :rdf/type
   :sub-class-of        :rdfs/subClassOf
   :sub-property-of     :rdfs/subPropertyOf
   :domain              :rdfs/domain
   :range               :rdfs/range
   :equivalent-class    :owl/equivalentClass
   :inverse-of          :owl/inverseOf
   :transitive-property :owl/TransitiveProperty
   :symmetric-property  :owl/SymmetricProperty})

(def iri-vocabulary
  "The same terms as the full IRIs an RDF import carries. `rdf:`, `rdfs:`
  and `owl:` expanded per their W3C namespace documents."
  {:type                "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
   :sub-class-of        "http://www.w3.org/2000/01/rdf-schema#subClassOf"
   :sub-property-of     "http://www.w3.org/2000/01/rdf-schema#subPropertyOf"
   :domain              "http://www.w3.org/2000/01/rdf-schema#domain"
   :range               "http://www.w3.org/2000/01/rdf-schema#range"
   :equivalent-class    "http://www.w3.org/2002/07/owl#equivalentClass"
   :inverse-of          "http://www.w3.org/2002/07/owl#inverseOf"
   :transitive-property "http://www.w3.org/2002/07/owl#TransitiveProperty"
   :symmetric-property  "http://www.w3.org/2002/07/owl#SymmetricProperty"})

(defn- terms
  "`vocabulary` with every key this namespace uses present, or a throw
  naming the ones that are not.

  A missing term must not default. A rule whose predicate position silently
  became `nil` matches no stored triple, so the rule contributes nothing and
  the query returns a smaller answer -- which is indistinguishable from an
  ontology that simply had no such axioms."
  [vocabulary]
  (let [required (set (keys keyword-vocabulary))
        missing (remove #(contains? vocabulary %) required)]
    (when (seq missing)
      (throw (ex-info "owl.rules: vocabulary is missing terms; a nil predicate would match nothing and read as an ontology without those axioms"
                      {:missing (vec (sort missing))})))
    vocabulary))

(defn hierarchy-rules
  "The class/property hierarchy closures, with every predicate a literal.

  | rule | RDFS | meaning |
  |------|------|---------|
  | `(owl-subclass ?a ?b)`    | rdfs11 | `?a` is a `?b`, transitively |
  | `(owl-subproperty ?a ?b)` | rdfs5  | property `?a` implies `?b`, transitively |
  | `(owl-type ?i ?c)`        | rdfs9  | `?i` is a `?c`, following the class hierarchy |

  `owl:equivalentClass` is folded in as subsumption in both directions,
  which is exactly what it means and is the only OWL term here that is not
  RDFS. It is included because an ontology that declares two classes
  equivalent and then finds a query answering for only one of them is
  reporting a wrong answer, not a narrow one.

  `owl-type` recurses through ITSELF rather than through the asserted
  `rdf:type` triple. The difference only shows when a type came from
  somewhere other than an assertion -- `triple-rules` adds `rdfs:domain`
  and `rdfs:range`, and a class hierarchy that could not be climbed from an
  inferred type would answer a strict subset without saying so.

  An engine that plans reads per predicate touches four ranges for these:
  `type`, `subClassOf`, `subPropertyOf`, `equivalentClass`."
  ([] (hierarchy-rules keyword-vocabulary))
  ([vocabulary]
   (let [{:keys [type sub-class-of sub-property-of equivalent-class]} (terms vocabulary)]
     [;; rdfs11 -- subClassOf is transitive
      ['(owl-subclass ?a ?b) ['?a sub-class-of '?b]]
      ['(owl-subclass ?a ?b) ['?a equivalent-class '?b]]
      ['(owl-subclass ?a ?b) ['?b equivalent-class '?a]]
      ['(owl-subclass ?a ?b) ['?a sub-class-of '?z] '(owl-subclass ?z ?b)]
      ;; rdfs5 -- subPropertyOf is transitive
      ['(owl-subproperty ?a ?b) ['?a sub-property-of '?b]]
      ['(owl-subproperty ?a ?b) ['?a sub-property-of '?z] '(owl-subproperty ?z ?b)]
      ;; rdfs9 -- type follows the class hierarchy, from wherever the type came
      ['(owl-type ?i ?c) ['?i type '?c]]
      ['(owl-type ?i ?c) '(owl-type ?i ?d) '(owl-subclass ?d ?c)]])))

(defn triple-rules
  "Generalized-triple entailment. `(owl-triple ?s ?p ?o)` holds for every
  asserted triple and every one the property-level RDFS/OWL RL rules derive
  from it; class membership stays on `(owl-type ?i ?c)`, which these rules
  extend with `rdfs:domain` and `rdfs:range`.

  | rule | source | |
  |------|--------|--|
  | base     | | every asserted `[?s ?p ?o]` |
  | rdfs7    | `rdfs:subPropertyOf` | a sub-property's triples are the super-property's |
  | rdfs2    | `rdfs:domain` | the subject of a domain-typed property gets that type |
  | rdfs3    | `rdfs:range`  | so does the object |
  | prp-trp  | `owl:TransitiveProperty` | the property's own transitive closure |
  | prp-symp | `owl:SymmetricProperty`  | the property read backwards |
  | prp-inv  | `owl:inverseOf` | the other property read backwards, both ways |

  **This ruleset reads the whole graph.** Its base case is `[?s ?p ?o]`
  with the predicate unbound, so no predicate index applies. That is not an
  implementation shortfall to be optimised away later -- deriving triples
  whose predicate is a variable is what these entailments MEAN, and the
  scan is the cost of the meaning. Use `hierarchy-rules` when the question
  is about classes, which is most of the time.

  Two entailments compose here that cannot compose in a single pass, which
  is the reason this is a fixpoint and not a materialisation step: the
  transitive-property rule derives through DERIVED triples, so the inverse
  of a transitive property closes correctly; and `rdfs:domain` feeds
  `owl-type`, which then climbs the class hierarchy.

  One deliberate gap: a triple whose predicate is a SUB-PROPERTY of
  `rdf:type` does not become an `owl-type` fact. Writing that rule needs
  `rdf:type` itself in a rule HEAD, where this engine takes only logic
  variables. Declaring a sub-property of `rdf:type` is disallowed in OWL 2
  DL and vanishingly rare elsewhere, so this is recorded rather than
  worked around -- an unstated gap is the failure; a stated one is a
  boundary."
  ([] (triple-rules keyword-vocabulary))
  ([vocabulary]
   (let [{:keys [type domain range inverse-of
                 transitive-property symmetric-property]} (terms vocabulary)]
     (into
      (hierarchy-rules vocabulary)
      [;; every asserted triple
       '[(owl-triple ?s ?p ?o) [?s ?p ?o]]
       ;; rdfs7 -- p rdfs:subPropertyOf q, s p o  =>  s q o
       ['(owl-triple ?s ?q ?o) '(owl-subproperty ?p ?q) '(owl-triple ?s ?p ?o)]
       ;; rdfs2 / rdfs3 -- domain and range induce class membership
       ['(owl-type ?s ?c) ['?p domain '?c] '(owl-triple ?s ?p ?o)]
       ['(owl-type ?o ?c) ['?p range '?c] '(owl-triple ?s ?p ?o)]
       ;; prp-trp -- a transitive property closes over the DERIVED triples
       ['(owl-triple ?x ?p ?z) ['?p type transitive-property]
        '(owl-triple ?x ?p ?y) '(owl-triple ?y ?p ?z)]
       ;; prp-symp -- a symmetric property reads backwards
       ['(owl-triple ?y ?p ?x) ['?p type symmetric-property] '(owl-triple ?x ?p ?y)]
       ;; prp-inv -- inverseOf, in both directions, because the axiom is
       ;; symmetric and an ontology states it once
       ['(owl-triple ?y ?q ?x) ['?p inverse-of '?q] '(owl-triple ?x ?p ?y)]
       ['(owl-triple ?y ?p ?x) ['?p inverse-of '?q] '(owl-triple ?x ?q ?y)]]))))
