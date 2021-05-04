# Changelog (unreleased)

## [Unreleased]

### Added

- in `ereal.v`:
  + definitions `dual_adde`
  + notations for the above in scope `ereal_dual_scope` delimited by `dE`
  + lemmas `adde_le0`, `sume_le0`, `oppe_ge0`, `oppe_gt0`, `oppe_le0`,
    `oppe_lt0`, `lte_opp`, `gee_addl`, `gee_addr`, `lte_addr`,
    `gte_subl`, `gte_subr`, `lte_le_sub`, `lee_sum_npos_subset`,
    `lee_sum_npos`, `lee_sum_npos_ord`, `lee_sum_npos_natr`,
    `lee_sum_npos_natl`, `lee_sum_npos_subfset`, `lee_opp`
  + lemmas `dual_addeE`, `dual_sumeE`, `def_dual_addeE`, `daddEFin`,
    `dsumEFin`, `dsubEFin`, `dadde0`, `dadd0e`, `daddeC`, `daddeA`,
    `daddeAC`, `daddeCA`, `daddeACA`, `doppeD`, `daddeK`, `dsubeK`,
    `dsubee`, `dadde_eq_pinfty`, `daddooe`, `dadde_Neq_pinfty`,
    `dadde_Neq_ninfty`, `desum_fset_pinfty`, `desum_pinfty`,
    `desum_fset_ninfty`, `desum_ninfty`, `dadde_ge0`, `dadde_le0`,
    `dsume_ge0`, `dsume_le0`, `dmule_ge0`, `dsube_lt0`, `dsubre_le0`,
    `dsuber_le0`, `dsube_ge0`, `lte_dadd`, `lee_daddl`, `lee_daddr`,
    `gee_daddl`, `gee_daddr`, `lte_daddl`, `lte_daddr`, `gte_dsubl`,
    `gte_dsubr`, `lte_dadd2lE`, `lee_dadd2l`, `lee_dadd2lE`,
    `lee_dadd2r`, `lee_dadd`, `lte_le_dadd`, `lee_dsub`,
    `lte_le_dsub`, `lee_dsum`, `lee_dsum_nneg_subset`,
    `lee_dsum_npos_subset`, `lee_dsum_nneg`, `lee_dsum_npos`,
    `lee_dsum_nneg_ord`, `lee_dsum_npos_ord`, `lee_dsum_nneg_natr`,
    `lee_dsum_npos_natr`, `lee_dsum_nneg_natl`, `lee_dsum_npos_natl`,
    `lee_dsum_nneg_subfset`, `lee_dsum_npos_subfset`,
    `lte_dsubl_addr`, `lte_dsubl_addl`, `lte_dsubr_addr`,
    `lee_dsubr_addr`, `lee_dsubl_addr`, `lee_dadde`, `lte_spdaddr`

### Changed

- in `normedtype.v`:
  + remove useless parameter from lemma `near_infty_natSinv_lt`

- in `ereal.v`:
  + lemmas `ge0_adde_def`, `onee_neq0`, `mule0`, `mul0e`
  + lemmas `mulrEDr`, `mulrEDl`, `ge0_muleDr`, `ge0_muleDl`
  + lemmas `ge0_sume_distrl`, `ge0_sume_distrr`
  + lemmas `mulEFin`, `mule_neq0`, `mule_ge0`, `muleA`
  + lemma `muleE`
  + lemmas `muleN`, `mulNe`, `muleNN`, `gee_pmull`, `lee_mul01Pr`
  + lemmas `lte_pdivr_mull`, `lte_pdivr_mulr`, `lte_pdivl_mull`, `lte_pdivl_mulr`,
    `lte_ndivl_mulr`, `lte_ndivl_mull`, `lte_ndivr_mull`, `lte_ndivr_mulr`
  + lemmas `lee_pdivr_mull`, `lee_pdivr_mulr`, `lee_pdivl_mull`, `lee_pdivl_mulr`,
    `lee_ndivl_mulr`, `lee_ndivl_mull`, `lee_ndivr_mull`, `lee_ndivr_mulr`
  + lemmas `mulrpinfty`, `mulrninfty`, `mule_gt0`
- in `normedtype.v`:
  + lemma `mule_continuous`

### Changed

- in `ereal.v`:
  + change definition `mule` such that 0 x oo = 0
  + `adde` now defined using `nosimpl` and `adde_def`

### Renamed

- in `ereal.v`:
  + `adde` -> `adde_def`
  + `adde_def` -> `adde_defined`
  + `adde_defC` -> `adde_definedC`
  + `ge0_adde_def`-> `ge0_adde_defined`
  + `fin_num_adde_def` -> `fin_num_adde_defined`
  + `adde_def_nneg_series` -> `adde_defined_nneg_series`

### Removed

### Infrastructure

### Misc
