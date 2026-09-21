import VennTopology

-- These examples are compiled type ascriptions, not textual name checks.
example :
    Venn19.Topology.SimpleRotationalVenn
      Venn19.Topology.rotationalVennCurve
      Venn19.Topology.rotationalVennSide :=
  Venn19.Topology.supplied_simple_rotational_venn

example :
    ∃ (C : Fin 19 → Set Venn19.Topology.Plane)
      (S : Fin 19 → Bool → Set Venn19.Topology.Plane),
      Venn19.Topology.SimpleRotationalVenn C S :=
  Venn19.Topology.exists_simple_rotational_venn_19

#eval IO.println "BEGIN supplied_simple_rotational_venn CHECK"
#check Venn19.Topology.supplied_simple_rotational_venn
#eval IO.println "END supplied_simple_rotational_venn CHECK"
#eval IO.println "BEGIN supplied_simple_rotational_venn PRINT"
#print Venn19.Topology.supplied_simple_rotational_venn
#eval IO.println "END supplied_simple_rotational_venn PRINT"

#eval IO.println "BEGIN exists_simple_rotational_venn_19 CHECK"
#check Venn19.Topology.exists_simple_rotational_venn_19
#eval IO.println "END exists_simple_rotational_venn_19 CHECK"
#eval IO.println "BEGIN exists_simple_rotational_venn_19 PRINT"
#print Venn19.Topology.exists_simple_rotational_venn_19
#eval IO.println "END exists_simple_rotational_venn_19 PRINT"
