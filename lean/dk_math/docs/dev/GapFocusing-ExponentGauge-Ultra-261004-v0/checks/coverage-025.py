"""Generate complete named public declaration coverage, not only a chosen sample."""
from pathlib import Path
import subprocess, re, json
base=Path(__file__).resolve().parent.parent
root=base.parents[2]
prod=['DkMath/NumberTheory/BinomialPrime.lean','DkMath/NumberTheory/BinomialPrimePower.lean','DkMath/NumberTheory/PascalPrebirthBoundary.lean','DkMath/NumberTheory/PascalPrebirthBirth.lean','DkMath/NumberTheory/Legendre/GnomonPascalCell.lean']
tests=['DkMathTest/NumberTheory/PascalPrebirthRegression.lean','DkMathTest/NumberTheory/LegendrePascalCellCalibration.lean']
pattern=re.compile(r'^(?:@\[[^\n]+\]\s*)?(?:(?:noncomputable|protected)\s+)?(?:def|theorem|lemma|abbrev)\s+([A-Za-z0-9_.]+)',re.M)
coverage=[];new=[]
for name in prod+tests:
    path=root/name
    text=path.read_text()
    declarations=pattern.findall(text)
    prefix='DkMath.NumberTheory.Legendre' if '/Legendre/' in name else 'DkMath.NumberTheory'
    if name in tests: prefix=name[:-5].replace('/','.')
    old=subprocess.run(['git','show','HEAD:lean/dk_math/'+name],capture_output=True,text=True)
    oldnames=set(pattern.findall(old.stdout)) if old.returncode==0 else set()
    coverage.append(dict(file=name,declarations=[prefix+'.'+d for d in declarations],new=[prefix+'.'+d for d in declarations if d not in oldnames]))
    new += coverage[-1]['new']
header= (root/prod[2]).read_text().split('import ')[0]
s=header+'\n'.join('import '+n[:-5].replace('/','.') for n in tests)+'\n\n#print "file: DkMathTest.NumberTheory.PascalPrebirthAxiomAudit"\n\n'
signature_checks=['Choose.lucas_theorem_nat','Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat','Choose.gcd_choose_eq_minFac_of_isPrimePow','Choose.gcd_choose_eq_one_of_not_isPrimePow','Nat.factorization_choose','Nat.factorization_choose_le_log','Nat.factorization_choose_le_one','Nat.factorization_choose_eq_zero_of_lt','DkMath.NumberTheory.AllInnerChooseDivisible','DkMath.NumberTheory.InnerRowSupportPrime','DkMath.NumberTheory.RowBirthPrime','DkMath.NumberTheory.PrimePowerRowSupport','DkMath.NumberTheory.PrimePrebirthAlternation','DkMath.NumberTheory.prime_prebirthAlternation_step','DkMath.NumberTheory.prime_prebirthAlternation','DkMath.NumberTheory.prime_power_allInnerChooseDivisible','DkMath.NumberTheory.prime_power_rowBirthPrime','DkMath.NumberTheory.padicValNat_choose_prime_pow','DkMath.NumberTheory.padicValNat_choose_prime_pow_add_index','DkMath.NumberTheory.pascalPrimeDialHeight_prime_pow_add_index','DkMath.NumberTheory.pascalPrimeDialHeight_prime_pow','DkMath.NumberTheory.prime_power_unitFilteredPrimeDialHeight','DkMath.NumberTheory.prime_not_dvd_pascalCoeffMass_of_row_lt','DkMath.NumberTheory.pascalPrimeCoordinateBirthSupport','DkMath.NumberTheory.pascalPrimeBirthLogMass','DkMath.NumberTheory.pascalPrimeBirthLogMass_eq','DkMath.NumberTheory.pascalPrimeCoordinateSupportUpTo_succ','DkMath.Pascal.WallisGrowthBridge.centralRatioQ_sq_eq_odd_mul_wallisPartialQ','DkMath.Pascal.WallisCellGrowth.pascalCellGrowthQ_eq_cast_choose']
s+='-- Installed source API signature checks.\n'+'\n'.join('#check '+name for name in signature_checks)+'\n\n'
for row in coverage:
    s+='-- Complete named public coverage of '+row['file']+'\n'
    s+='\n'.join('#print axioms '+d for d in row['declarations'])+'\n\n'
(root/'DkMathTest/NumberTheory/PascalPrebirthAxiomAudit.lean').write_text(s.rstrip()+'\n')
result=dict(scope='All named public declarations of five changed production source modules and two new calibration modules',production_count=sum(len(r['declarations']) for r in coverage[:len(prod)]),calibration_count=sum(len(r['declarations']) for r in coverage[len(prod):]),new_production_count=sum(len(r['new']) for r in coverage[:len(prod)]),new_calibration_count=sum(len(r['new']) for r in coverage[len(prod):]),total=sum(len(r['declarations']) for r in coverage),modules=coverage)
(base/'logs/declaration-coverage-025.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='modules'},indent=2))
