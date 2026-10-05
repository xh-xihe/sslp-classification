"""Refresh progress while preserving immutable prior proof acceptance."""
from collections import Counter
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
EVIDENCE = ROOT/'artifacts/manuscript-certification-20261005'
sys.path.insert(0,str(ROOT/'tools'))
import verify


def write(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2)+'\n', encoding='utf8')


def main():
    ledger = json.loads((ROOT/'results/paper-claims-20261003.json').read_text(encoding='utf8'))
    catalog = json.loads((ROOT/'results/proof-modules.json').read_text(encoding='utf8'))
    counts = dict(sorted(Counter(c['status'] for c in ledger['claims']).items()))
    types = json.loads((EVIDENCE/'kernel-types-orbit31-support.json').read_text(encoding='utf8'))
    run_path = EVIDENCE/'run.json'
    run = json.loads(run_path.read_text(encoding='utf8'))
    run.update(active_lean_modules=catalog['module_count'], current_claim_status_counts=counts)
    run['whole_build'] = {'status':'running', 'modules':catalog['module_count'],
                          'log':'orbit31-support-full-build.log'}
    run['axiom_audit'] = {'status':'pending_fresh_union_audit'}
    record = {'record':'kernel-types-orbit31-support.json','declarations':len(types['declarations'])}
    run['kernel_type_inspections'] = [r for r in run['kernel_type_inspections'] if r['record'] != record['record']]+[record]
    run['correspondence_gates'] = {'status':'pending_fresh_gates',
                                 'scope':'New proof batch does not finish all SI correspondence or held main issues.'}
    write(run_path, run)
    status_path = ROOT/'results/repository-status.json'
    status = json.loads(status_path.read_text(encoding='utf8'))
    status.update(active_lean_modules=catalog['module_count'], current_claim_status_counts=counts,
                  current_type_inspection_declarations=len(types['declarations']),
                  planned_axiom_roots=len(verify.axiom_inventory(paper_version='20261003')[0]))
    status['pending_proof_batch'] = {
        'record':'artifacts/manuscript-certification-20261005/orbit31-support-work-in-progress.json',
        'scope':'Complete real support counts, physical signed-graph bridge, actual table symmetry, '
                '204-vertex completeness, coordinate-face convex hulls and thirteen literal branch certificates. '
                'Strict pilots pass; the new whole build and fresh transitive audit are pending.'}
    write(status_path, status)
    wip = {
        'schema':1, 'status':'in_progress_whole_snapshot',
        'scope':'Candidate data remain untrusted inputs. The listed Lean theorems have strict pilots; '
                'whole-build/axiom acceptance and canonical publication of this batch remain pending.',
        'candidate_data':'results/orbit31-support-candidates-20261005.json',
        'active_lean_modules':catalog['module_count'],
        'kernel_type_evidence':'kernel-types-orbit31-support.json',
        'physical_reduced_moments_and_complete_moment_equivalence':'strict_PASS',
        'all_65536_masks_real_primal_dual_semantics':'strict_PASS',
        'exact_support_count_15603':'strict_PASS',
        'physical_cross_rows_all_twelve_flip_systems':'content_validated_dependency_build_PASS',
        'physical_phase_edges_and_no_singleton':'strict_PASS',
        'no_singleton_count_2903':'content_validated_dependency_build_PASS',
        'all_2903_phase_certificates_and_exhaustion':'content_validated_dependency_build_PASS',
        'signed_phase_survivor_count_311':'strict_PASS',
        'literal_sixteen_representatives_orbit_sizes_and_exhaustion':'strict_PASS',
        'actual_affine_group_iso_and_physical_symmetry':'strict_PASS',
        'all_204_vertices_and_support_counts_108_96':'strict_PASS',
        'all_coordinate_face_convex_hulls':'strict_PASS',
        'eleven_direct_triangle_branches':'strict_PASS',
        'type1_mixed_triangle':'strict_PASS',
        'type2_cross_common_product_actual_same_state_and_no_go':'strict_PASS',
        'literal_type9_type14_type16_derivations':'pending_current_SI_correspondence',
        'whole_build_log':'orbit31-support-full-build.log',
        'last_accepted_proof_snapshot':status['last_accepted_local_proof_snapshot'],
    }
    write(EVIDENCE/'orbit31-support-work-in-progress.json', wip)
    print(f'Progress refreshed: {catalog["module_count"]} active modules, {counts["covered"]} covered, '
          f'{counts["unreviewed"]} SI assertions pending; prior acceptance retained')


if __name__ == '__main__':
    main()
