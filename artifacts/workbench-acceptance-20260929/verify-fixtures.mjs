// Generate portable manual-acceptance inputs and check expectations with the current engine.
// This does not execute the hosted UI, the project API, or Lean.
import {readFileSync,writeFileSync} from 'node:fs';
import assert from 'node:assert/strict';
import {parseCode,checkCode,exactText} from '../../apps/sslp-explorer/app/lib/workbench.ts';
const coordinates=[1,0,0,0,0,0,0,0];
const row=bits=>({bits,coordinates:[...coordinates]});
const passing={schema:'sslp.research-code.v1',n:4,k:2,distance:2,denominator:2,q:4,angles:[1,1,1,1],words:[[row('0000'),row('1111')],[row('0011'),row('1100')]]};
const failing=structuredClone(passing);
failing.words[1]=[{bits:'0011',coordinates:[0,1,0,0,0,0,0,0]}];
const unsupported={...structuredClone(passing),n:7,angles:[1,1,1,1,0,0,0],words:passing.words.map(w=>w.map(a=>({...a,bits:a.bits+'000'})))};
const write=(name,value)=>writeFileSync(new URL(name,import.meta.url),JSON.stringify(value,null,2)+'\n');
write('01-pass-four-qubit.json',passing);
write('02-fail-kl-four-qubit.json',failing);
write('03-unsupported-seven-qubit.json',unsupported);
function summary(code){const r=checkCode(code),f=r.rows.find(x=>!x.passed);return {
  normalized:r.normalized,kl_passed:r.passed,passed_paulis:r.rows.filter(x=>x.passed).length,total_paulis:r.rows.length,
  diagonal_action:r.diagonalAction,residues:r.fibers,kernel_status:r.kernel,
  first_failure:f?{pauli:f.pauli,matrix:f.matrix_coordinates.map(line=>line.map(v=>exactText(v,code.denominator)))}:null,
};}
const a=summary(passing),b=summary(failing);
assert.equal(a.kl_passed,true);assert.equal(a.total_paulis,13);assert.deepEqual(a.residues,[[0],[2]]);
assert.equal(b.normalized,true);assert.equal(b.kl_passed,false);assert.equal(b.passed_paulis,9);
assert.deepEqual(b.first_failure,{pauli:'Z1',matrix:[['0','0'],['0','1']]});
let rejection='';try{parseCode(JSON.stringify(unsupported))}catch(e){rejection=e.message}
assert.equal(rejection,'Qubit count must be an integer from 1 to 6.');
const template=JSON.parse(readFileSync(new URL('../../apps/sslp-explorer/app/data/class36.json',import.meta.url),'utf8'));
const canonical=parseCode(JSON.stringify(template.instance)),modified=structuredClone(canonical);
modified.words[0][0].coordinates=modified.words[0][0].coordinates.map(v=>-v);
const wrongGate=structuredClone(canonical);wrongGate.angles[4]=1;
const wrongGateSummary=summary(wrongGate);
assert.equal(wrongGateSummary.passed_paulis,154);assert.equal(wrongGateSummary.diagonal_action,false);
const expected={schema:'sslp.manual-acceptance-expectations.v1',scope:'Fixture computations only; not hosted UI acceptance or Lean execution',
  four_qubit_pass:a,four_qubit_fail:b,unsupported_import_error:rejection,
  class36:summary(canonical),class36_first_amplitude_sign_flip:{bits:modified.words[0][0].bits,...summary(modified)},class36_q5_exponent_changed_to_one:wrongGateSummary};
write('expected-results.json',expected);
console.log(JSON.stringify(expected,null,2));
