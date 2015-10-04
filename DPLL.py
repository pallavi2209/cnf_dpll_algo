import sys
import argparse
import copy

# enum for different connectives
def enum(**enums):
    return type('Enum', (), enums)
Conn = enum(IFF = "iff", IMPLIES="implies", AND="and", OR='or' , NOT = "not")

# print in symbols to ease in reading
def toSymbolString(pList):
  if isinstance(pList, str) and pList[0].isupper():
    return pList
  elif pList[0] == Conn.NOT:
    return "~" + toSymbolString(pList[1])
  elif pList[0] == Conn.AND:
    return "(" + " ^ ".join(map(toSymbolString, pList[1:])) + ")"
  elif pList[0] == Conn.OR:
    return "(" + " V ".join(map(toSymbolString, pList[1:])) + ")"
  elif pList[0] == Conn.IMPLIES:
    return "(" + toSymbolString(pList[1]) + " => " + toSymbolString(pList[2]) + ")"
  elif pList[0] == Conn.IFF:
    return "(" + toSymbolString(pList[1]) + " <=> " + toSymbolString(pList[2]) + ")"

def ifClauseSatisfy(clause, model):
  ## if emplty clause, return false
  if len(clause) == 0:
    return False
  # return value of literal in model if present, else return none
  elif type(clause) == str:
    if clause in model:
      return model[clause]
    else:
      return None
  # if literal not in model, return None, else return opposite of literal value in model
  elif clause[0] == Conn.NOT:
    if clause[1] in model:
      return (not model[clause[1]])
    else:
      return None
  elif clause[0] == Conn.OR:
    ## if empty clause, return false
    ## if non empty clause, if any one is true, return true, if all False, return False, else return None
    seen = True
    for cls in clause[1:]:
       clm = ifClauseSatisfy(cls, model)
       if clm == None:
         seen = False
       if clm == True:
         return True
    if seen == False:
      return None
    else:
      return False

def find_Pure_Symbol(symbols, clauses):
  ## make a dictionary which has structure as symbol -> {if Positive Present, if Negative Present}. Example: {A:{0,1}} means Not A is present in clauses, 0- > No, 1 -> Yes
  dictSymb = {}
  for symb in symbols:
    dictSymb[symb] = [0,0]
  for cl in clauses:
    if type(cl) == str:
      dictSymb[cl][0] = 1
    elif cl[0] == Conn.NOT:
      dictSymb[cl[1]][1] = 1
    elif cl[0] == Conn.OR:
      for literal in cl[1:]:
        if type(literal) == str:
          dictSymb[literal][0] = 1
        elif literal[0] == Conn.NOT:
          dictSymb[literal[1]][1] = 1
  ## make a list of pure literals, in which either(symbol or ~symbol) of symbol values are present
  pureLiterals = []
  for s, sPair in dictSymb.items():
    if not sPair[0] == sPair[1]:
      if sPair[0] ==1:
        pureLiterals.append((s, True))
      else:
        pureLiterals.append((s, False))
  return pureLiterals

def updateClause(clausesToUpdate, symbol, value):

  retClauses = []
  for clauseTU in clausesToUpdate:
    ## if string literal, remove clause if it is same literal. If opposite literal, then remove opposite literal from clause and add empty clause instead. Otherwise, keep the clause
    if type(clauseTU) == str:
      if symbol == clauseTU:
        if value == False:
          retClauses.append([])
      else:
        retClauses.append(clauseTU)
    ## If not literal, remove clause if not literal, else add empty clause, if opposite literal. If none, keep the clause
    elif clauseTU[0] == Conn.NOT:
      if symbol == clauseTU[1]:
        if value == True:
          retClauses.append([])
      else:
        retClauses.append(clauseTU)
    ## If an operand of OR is true, remove the clause. If opposite of operand is true (in case of unit literal), remove the operand from the clause. If all removed, add empty clause.
    elif clauseTU[0] == Conn.OR:
      orClause = [Conn.OR]
      seenTrue = False
      for subclause in clauseTU[1:]:
        ## handle case of string literal, as explained above
        if type(subclause) == str:
          if symbol == subclause:
            if value == True:
              seenTrue = True
              break
          else:
            orClause.append(subclause)
        ## handle case of NOT literal, as explained above
        elif subclause[0] == Conn.NOT:
          if symbol == subclause[1]:
            if value == False:
              seenTrue = True
              break
          else:
            orClause.append(subclause)
      if not seenTrue:
        if len(orClause) == 1:
          retClauses.append([])
        else:
          retClauses.append(orClause)
  return retClauses


def find_Unit_Clause(clauses):
  unitLiterals = []
  # make a list of tuples (literal, value) for single literals and not literals
  for aClause in clauses:
    if type(aClause) == str:
      # check for repeating literals in unit literal, add only unique
      sameLiteral = filter(lambda x: x[0] == aClause, unitLiterals)
      if not sameLiteral:
        unitLiterals.append((aClause, True))
    elif aClause[0] == Conn.NOT:
    # check for repeating literals in unit literal, add only unique
      sameLiteral = filter(lambda x: x[0] == aClause[1], unitLiterals)
      if not sameLiteral:
        unitLiterals.append((aClause[1], False))
  return unitLiterals


def DPLL(clauses, symbols, model):
  #print "symbols: " + str(symbols)
  #print "model: " + str(model)
  #print "clauses: " + str(clauses)


  for clause in clauses:
    # check if each clause satisfy
    clRes = ifClauseSatisfy(clause, model)
    # if some clause is undecidable because of incomplete model, then continue to select symbol values(completing model)
    if clRes == None:
      ## find list of pure symbols and their values

      retPureLiterals = find_Pure_Symbol(symbols, clauses)
      #print "retPureLiterals: " + str(retPureLiterals)
      if len(retPureLiterals) > 0:
        for pureL in retPureLiterals:
          (symP, valueP) = pureL
          symbols.remove(symP)
          model[symP] = valueP
        # update clause, remove satisfied clauses completely which contains literal, remove opposite literal from other clauses
          clauses = updateClause(clauses, symP, valueP)
        return DPLL(clauses, symbols, model)
      ## find list of unit clause symbols and their values
      retUnitClauses = find_Unit_Clause(clauses)
      #print "retUnitClauses: " + str(retUnitClauses)
      if len(retUnitClauses)>0:
        for unitClause in retUnitClauses:
          (symU, valueU) = unitClause
          symbols.remove(symU)
          model[symU] = valueU
          clauses = updateClause(clauses, symU, valueU)
        return DPLL(clauses, symbols, model)
      # apply brute force, if no unit or pure symbol found. Recurse to find if new unit/pure symbols formed
      first = symbols[0]
      rest = symbols[1:]
      clausesT = updateClause(clauses, first, True)
      model[first] = True
      firstT = DPLL(clausesT, rest, model)
      ## if first case, (literal = true) return true, update symbols,  model and clause.
      if firstT == True:
        symbols.remove(first)
        #model[first] = True
        clauses = updateClause(clauses, first, True)
        return True
      ## otherwise, test 2nd case in which literal = False
      else:
        clausesF = updateClause(clauses, first, False)
        model[first] = False
        firstF = DPLL(clausesF, rest, model)
        if firstF == True:
          symbols.remove(first)
          clauses = updateClause(clauses, first, False)
          return True
        else:
          del model[first]
          return False
    if clRes == False:
      return False
  return True
    

def DPLL_Satisfiable(pSentence):
  pList = eval(pSentence)
  #print pList
  #print toSymbolString(pList)
  clauses = []
  ## make a list of clauses in sentence
  if type(pList) == str or pList[0] == Conn.NOT or pList[0] == Conn.OR:
    clauses.append(pList)
  elif pList[0] == Conn.AND:
    clauses.extend(pList[1:])

  ## make a list of unique symbols from clauses
  symbols = set()
  for cls in clauses:
    if type(cls) == str:
      symbols.add(cls)
    elif cls[0] == Conn.NOT:
      symbols.add(cls[1])
    elif cls[0] == Conn.OR:
      for sym in cls[1:]:
        if type(sym) == str:
          symbols.add(sym)
        elif sym[0] == Conn.NOT:
          symbols.add(sym[1])
  symbols = list(symbols)
  model = {}
  result =  DPLL(clauses, symbols, model)
  return (result, model)

def DPLLMain(argv):
  parser = argparse.ArgumentParser()
  # add required option -i 
  parser.add_argument('-i', dest='inputfilename', required = True)
  args = parser.parse_args(argv)
  infname = args.inputfilename
  ## open input file and read
  infile = open(infname, "r")
  outfile = open("CNF_satisfiability.txt", "w")
  indata = infile.readlines()

  numLines = int(indata[0])
  for i in range(1, numLines+1):
    pSentence = indata[i]
    #print "\n"
    #print "Sentence: " + str(i)
    try:

      (result, model) = DPLL_Satisfiable(pSentence)
    except:
      outfile.write("\n")
    else:
      resList = [(str(result)).lower()]
      # make a string in required output format
      if result == True:
        for k, v in model.items():
          strVal = k + "=" + (str(v)).lower()
          resList.append(strVal)
      ## write to output file with newline at end
      outfile.write(str(resList))
      if not i == numLines:
        outfile.write("\n")
  infile.close()
  outfile.close()

if __name__=="__main__":
  DPLLMain(sys.argv[1:])