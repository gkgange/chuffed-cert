#!/bin/bash
CCP_BASE=~/postdoc/certification/cert-cp
MZN2FZN=mzn2fzn
FZN2CMOD=${CCP_BASE}/fzn2cmod/fzn2cmod
FDRES_SIMP=${CCP_BASE}/fdres/fdres-simp
FDRES_CHECK=${CCP_BASE}/fdres/fdres-check
CCP_STREAM=${CCP_BASE}/checker/certcp_stream
TEMPFILE=tempfile

## Build model
fzn_model=`${TEMPFILE} --suffix=.fzn`
ccp_model=`${TEMPFILE} --suffix=.fzn`
chuffed_out=`${TEMPFILE}`

${MZN2FZN} -G chuffed-cert -o ${fzn_model} $@

${FZN2CMOD} ${fzn_model} > ${ccp_model}
if [ $? -ne 0 ]
then
  exit 1
fi

./fzn_chuffed -S -f -logging=true ${fzn_model} | tee ${chuffed_out}

## Figure out what mode we're running in.
## ==============
args="${ccp_model}"

## A solution was found
grep -q -e "--------" ${chuffed_out}
if [ $? -eq 0 ]
then
  args="${args} -solution log.sol"
fi

## Unsatisfiability was proven
grep -q -e "=======" ${chuffed_out}
if [ $? -eq 0 ]
then
  ${FDRES_SIMP} log.lit log.dres > log.fdres
  echo -n "Checking FD resolution trace... "
  ${FDRES_CHECK} log.fdres
  if [ $? -ne 0 ]
  then
    echo "failed."
    exit 1
  fi
  args="${args} -trace log.fdres"
#  args="${args} -trace log.dres -lits log.lit"
fi

solve_line=`tail -n 1 ${fzn_model}`
obj_decl=`echo ${solve_line} | grep -o -e "minimize *[a-zA-Z_][a-zA-Z0-9_]*"`
if [ $? -eq 0 ]
then
  args="${args} -objective `echo ${obj_decl} | awk '{ print $2; }'`"
else
  echo ${solve_line} | grep -q "maximize"
  if [ $? -eq 0 ]
  then
    echo "ERROR: certcp_stream cannot currently handle maximization."
    exit 1
  fi
fi
  
echo -n "Running certified checker..."
${CCP_STREAM} ${args}
if [ $? -ne 0 ]
then
  cp ${ccp_model} debug.cmod
  cp ${fzn_model} debug.fzn
  rm ${fzn_model}
  rm ${ccp_model}
  exit 1
fi

## Cleanup
rm ${fzn_model}
rm ${ccp_model}
rm ${chuffed_out}
rm log.{sol,lit,dres,fdres}
