"""Source-reference and preservation audit for the Outcome C checkpoint.

This checks source locations and unchanged files, not mathematical entailment.
It neither invokes Lean nor treats earlier build logs as a new build.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess

base = Path(__file__).resolve().parent.parent
root = base.parents[2]
anchors = {
    'Basic': ['CounterexamplePack'],
    'SevenBaseTerminalRamifiedSummit': ['PrimitiveRamifiedSummitPacket'],
    'SevenBaseTerminalRamifiedCanonicalSplit': ['RamifiedSecondCoordinateCanonicalSplit'],
    'SevenBaseTerminalRamifiedQuadraticInnerRoot': [
        'RamifiedQuadraticInnerRootPacket', 'nonempty_quadraticInnerRoot',
        'coordinate_eq_fortyNine', 'innerRoot_coordinates_isCoprime',
        'innerRoot_norm_eq', 'inner_secondCoordinate_product_eq',
        'innerRootSnd_depth_eq_four', 'exists_inner_secondCoordinate_split'],
    'SevenBaseTerminalRamifiedRealCubicNorm': [
        'RamifiedRealCubicNormPacket', 'signedRootGap_seventhPower_eq',
        'sourceDifference_eq_normalizedAxis_pow_six_mul_pow_seven'],
    'SevenRealCubicInt': ['normalizedAxis', 'normalizedWitness',
        'ramifiedAxis_mul_seven_pow_four_mul_pow_seven'],
    'SevenRealCubicUnitClass': ['RamifiedRealCubicExactPowerPacket'],
    'SevenRealCubicAxisDrop': ['norm_leftRoot_eq_signedRoot',
        'norm_rightRoot_eq_signedRoot', 'signedRootGap_eq_norm_sub_norm',
        'RamifiedRealCubicDepthLedgerPacket', 'RamifiedRealCubicAxisDropPacket',
        'RamifiedRealCubicBalancedAxisSplitPacket'],
    'SevenRamifiedSignedRootDepth': ['RamifiedSignedRootDepthPacket'],
    'SevenRamifiedSignedRootRouting': ['RamifiedSignedRootRoutingPacket',
        'nonempty_coherent_signedRootRouting'],
    'CoprimeTripleRouting': ['CoprimeTripleRouting'],
    'SevenRamifiedFusionRoutingAudit': ['thirdRow_eq_one', 'activeCells_not_seven_dvd'],
    'SevenRamifiedFusionRealPairCoprimalityNormGate': [
        'c21_eq_quotientRoot_innerFst_gcd',
        'c22_eq_quotientRoot_innerFst_add_innerSnd_gcd',
        'Col3SeventhPowerSplit', 'nonempty_col3SeventhPowerSplit',
        'exists_row2_twoCellSeventhPowerFactor'],
    'SevenRamifiedFusionRealPairLoadAllocation': ['RealPairLoadedPowerSplit',
        'nonempty_realPairLoadedPowerSplit'],
    'SevenRamifiedFusionLoadedCore': ['RamifiedFusionLoadedCorePacket',
        'natAbs_norm_load21', 'natAbs_norm_load22'],
    'SevenRamifiedFusionLoadedResidualIdealBridge': ['row2ResidualNormRoot',
        'quotientRoot_natAbs_eq_row2Loads_mul_residualNormRoot_pow',
        'padicValNat_quotientRoot_eq_loads_add_seven_mul_residual'],
    'SevenRamifiedFusionCyclotomicDegreeSixCarrier': ['zeta_pow_seven', 'zeta_ne_one'],
    'SevenRamifiedFusionGlobalOrientedPrimeFactorization': ['GlobalOrientedPrimeFactorizationPacket'],
    'SevenRamifiedFusionSeventhPowerResidualIdealExtraction': [
        'globalOrientedLoadedHalfIdeal', 'globalOrientedResidualIdeal',
        'span_carrier_eq_loadedCarrier_mul_residual_pow'],
    'SevenRamifiedFusionElementLevelOrientedPower': ['OrientedElementLevelPowerWitness',
        'orientedElementLevelPowerWitness', 'orientedResidualRoot',
        'cyclotomicDegreeSixCarrier_eq_load_mul_residualRoot_pow'],
    'SevenRamifiedFusionCyclotomicAdditiveChartBoundary': [
        'sixPhaseProduct_eq_ofReal_cyclotomicNorm', 'zerothCoordinate_not_multiplicative',
        'no_ringHom_to_int', 'cyclotomicNorm_cyclotomicDegreeSixCarrier',
        'cyclotomicDegreeSixCarrier_coordinates', 'orientedElementLevelPower_additiveBoundary',
        'orientedResidualRoot_muSevenGaugeBoundary'],
    'SevenRamifiedFusionDirectChartObstruction': ['no_direct_signedFermatSevenChart'],
    'SevenRamifiedFusionStrictDescentFailureBoundary': ['internalDepthFourCarrier',
        'outerDepthFiveCarrier', 'InternalDepthFourCounterexampleReconstructionObligation',
        'internalDepthFourCounterexampleReconstructionObligation_iff_strictDescentCandidate',
        'exists_strict_awayCounterexample_of_internalDepthFourReconstruction'],
    'SevenRamifiedFusionDepthFourReconstructionAudit': [
        'internalDepthFourReconstructedRoute_root_depth',
        'internalDepthFourReconstructedRoute_root_ne_innerRoot',
        'no_fullCoordinate_decoder_on_orientedResidualIdeal'],
    'CoordinateNormalForm': ['AwayCoordinateNormalForm', 'coordinateCounterexampleRoute_of_pack'],
    'AwayValuationTransfer': ['AwayValuationTransferPacket', 'nonempty_awayValuationTransferPacket'],
    'SevenRamifiedFusionNestedReconstruction': ['internalDepthFourSeventhCore',
        'internalDepthFourCarrier_eq_seven_pow_four_mul_core_pow',
        'internalDepthFourSeventhCore_pos'],
    'SevenRamifiedFusionAllocationThreshold': ['internalDepthFourAllocation_strict_branch_selector',
        'RamifiedRealCubicNormPacket.exists_inner_complementary_seventh_root'],
    'SevenRamifiedFusionSixthPowerAllocationSieve': ['SixthPowerAllocationSieve',
        'sixthPowerAllocationSieve_mod_one'],
    'SevenRamifiedFusionCenteredPolynomial': ['centered_seventh_power_difference',
        'CenteredNestedAllocationCandidate', 'SixthPowerSievedCenteredCondition',
        'internalDepthFourReconstruction_iff_centered'],
    'SevenRamifiedFusionCenteredGnomonGap': ['internalDepthFourAllocation_excluded_of_perfectSixth',
        'internalDepthFourReconstruction_excluded_of_perfectSixth_family'],
}
source = []
for stem, names in anchors.items():
    path = root / 'DkMath/FLT/Seven' / (stem + '.lean')
    raw = path.read_bytes()
    text = raw.decode()
    locations = {}
    for name in names:
        pattern = (r'^(?:noncomputable )?(?:structure|def|theorem) '
                   + re.escape(name) + r'(?=\s|\()')
        matches = list(re.finditer(pattern, text, re.M))
        assert len(matches) == 1, (stem, name)
        locations[name] = text[:matches[0].start()].count('\n') + 1
    relative = str(path.relative_to(root))
    committed = subprocess.check_output(
        ['git', 'show', 'HEAD:lean/dk_math/' + relative], cwd=root)
    assert raw == committed, relative
    source.append({'path': relative, 'sha256': hashlib.sha256(raw).hexdigest(),
                   'unchanged_from_HEAD': True, 'declaration_lines': locations})

preserved = [
    'DkMath/FLT/Seven.lean', 'DkMath.lean',
    'DkMathTest/FLT/Seven/CenteredGnomonGapCalibration.lean',
    'DkMathTest/FLT/Seven/CenteredGnomonGapAxiomAudit.lean',
]
for relative in preserved:
    raw = (root / relative).read_bytes()
    assert raw == subprocess.check_output(
        ['git', 'show', 'HEAD:lean/dk_math/' + relative], cwd=root), relative
    source.append({'path': relative, 'sha256': hashlib.sha256(raw).hexdigest(),
                   'unchanged_from_HEAD': True})

assert not subprocess.check_output(['git', 'diff', 'HEAD', '--name-only', '--', '*.lean'], cwd=root)
assert not subprocess.check_output(
    ['git', 'ls-files', '--others', '--exclude-standard', '--', '*.lean'], cwd=root)
assert subprocess.run(['git', 'diff', '--check'], cwd=root).returncode == 0
report = base / 'report-051.md'
assert report.read_text().isascii()
for match in re.finditer(r'\]\((\.\./[^)]+)\)', report.read_text()):
    assert (base / match[1].split('#')[0]).exists(), match[1]
locations_by_path = {entry['path']: entry.get('declaration_lines', {}) for entry in source}
reference_pattern = (r'\]\(\.\./\.\./\.\./(DkMath/FLT/Seven/[^)]+)\),\s*'
                     r'lines?\s+([0-9]+(?:(?:,\s*|\s+and\s+)[0-9]+)*)')
for match in re.finditer(reference_pattern, report.read_text()):
    allowed = set(locations_by_path[match[1]].values())
    assert set(map(int, re.findall(r'\d+', match[2]))) <= allowed, match[0]
for path in [report, Path(__file__)]:
    assert all(line.rstrip() == line for line in path.read_text().splitlines()), path
data = {
    'outcome': 'C',
    'HEAD': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root).decode().strip(),
    'new_Lean_declarations': 0,
    'Lean_builds_run_for_051': 0,
    'facade_direct_imports': len(re.findall(r'^import ', (root / preserved[0]).read_text(), re.M)),
    'source_audit': source,
    'scope': 'Source locations and preservation only; no entailment or new kernel proof claimed.',
}
(base / 'logs/source-audit-051.json').write_text(json.dumps(data, indent=2) + '\n')
message = (f'PASS: Outcome C; {len(anchors)} referenced production sources and '
           f'{len(preserved)} preserved Lean files unchanged from HEAD; '
           f'{sum(len(v) for v in anchors.values())} declaration locations; '
           f'{data["facade_direct_imports"]} facade imports; report links and whitespace. '
           'No Lean build or new mathematical proof is claimed.\n')
(base / 'logs/check-051.txt').write_text(message)
print(message, end='')
