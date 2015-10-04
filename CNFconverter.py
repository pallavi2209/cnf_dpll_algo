import sys
import argparse

# enum for different connectives
def enum(**enums):
    return type('Enum', (), enums)
Conn = enum(IFF = "iff", IMPLIES="implies", AND="and", OR='or' , NOT = "not")

def eliminateIff(pList):
  if isinstance(pList, str) and pList[0].isupper():
    return pList
  elif pList[0] == Conn.NOT:
    return [pList[0] , eliminateIff(pList[1])]
  elif pList[0] == Conn.AND or pList[0] == Conn.OR or pList[0] == Conn.IMPLIES:
    rlist = [pList[0]]
    rlist.extend(map(eliminateIff, pList[1:]))
    return rlist
  elif pList[0] == Conn.IFF:
    return [Conn.AND , [ Conn.IMPLIES , eliminateIff(pList[1]) , eliminateIff(pList[2])] , [ Conn.IMPLIES , eliminateIff(pList[2]) , eliminateIff(pList[1])]]


def eliminateImplies(pList):
  if isinstance(pList, str) and pList[0].isupper():
    return pList
  elif pList[0] == Conn.NOT:
    return [pList[0], eliminateImplies(pList[1])]
  elif pList[0] == Conn.AND or pList[0] == Conn.OR:
    rlist1 = [pList[0]]
    rlist1.extend(map(eliminateImplies, pList[1:]))
    return rlist1
  elif pList[0] == Conn.IMPLIES:
    return [Conn.OR , [Conn.NOT, eliminateImplies(pList[1])], eliminateImplies(pList[2])]

def pushNegDown(pList):
  if isinstance(pList, str) and pList[0].isupper():
    return pList
  elif pList[0] == Conn.NOT:
    nVar = pList[1]
    if type(nVar) == str:
      return pList
    else:
      if nVar[0] == Conn.AND:
        return [Conn.OR] + map(lambda x: pushNegDown([Conn.NOT , x]), nVar[1:])
      elif nVar[0] == Conn.OR:
        return [Conn.AND] + map(lambda x: pushNegDown([Conn.NOT , x]), nVar[1:])
      elif nVar[0] == Conn.NOT:
        return pushNegDown(nVar[1])
  else:
    return [pList[0]] + map(pushNegDown, pList[1:])

def distribute(pList):
  #print(pList)
  if isinstance(pList, str) and pList[0].isupper():
    return pList
  elif pList[0] == Conn.NOT:
    return pList
  elif pList[0] == Conn.AND:
    childCNFsList = map(distribute, pList[1:])
    #print "childCNFsList"+str(childCNFsList)
    res = [pList[0]]
    for item in childCNFsList:
      if type(item) == list and item[0] == Conn.AND:
        res.extend(item[1:])
      else:
        res.append(item)
    return res
  # if OR is at root, I find the first AND child and distribute the remaining OR child operands over this AND. Simulatneously, if I get OR as a child of OR, I flatten it out.
  elif pList[0] == Conn.OR:
    alphaORs = []
    betaANDs = []
    for i in range(1, len(pList)):
      item = pList[i]
      #print item
      if type(item) == str:
        alphaORs.append(item)
      elif item[0] == Conn.NOT:
        alphaORs.append(item)
      elif item[0] == Conn.OR:
        # if root is OR and child is OR, distribute the child. If result is OR, flatten (add child OR operands to parent OR), else distribute
        rec = distribute(item)
        if rec[0] == Conn.OR:
          alphaORs.extend(rec[1:])
        elif rec[0] == Conn.AND:
          betaANDs = rec
          if i < (len(pList)-1):
            alphaORs.extend(pList[(i+1):])
          break;
      elif item[0] == Conn.AND:
        # got an AND as child, prepare to distribute.
        betaANDs = item
        if i < (len(pList)-1):
          alphaORs.extend(pList[(i+1):])
        break;
    # if alphaOR has only literal, then treat it as literal, else create OR cluase out of it
    if len(alphaORs) > 1:
      alphaORs.insert(0, Conn.OR)
    if len(betaANDs) == 0:
      if len(alphaORs) > 1:
        return alphaORs
      else:
        return alphaORs[0]
    else:
      # ditribute OR over AND
      res = [Conn.AND]
      for item in betaANDs[1:]:
        if len(alphaORs)>1:
          res.append(distribute([Conn.OR, alphaORs, item]))
        else:
          res.append(distribute([Conn.OR, alphaORs[0], item]))
      flattenRes = distribute(res)
      return flattenRes

# check if sentence pList1 is duplicate of tree pList2
def isSame(pList1, pList2):
  if type(pList1) == str and type(pList1) == str and pList1 == pList2:
    return True
  elif pList1[0] == Conn.NOT and pList2[0] == Conn.NOT:
    if pList1[1] == pList2[1]:
      return True;
  # if root is same, check if childs are same. check length first, if same length, then create a combined set. If length of combined set is equal to one of the list, then return true
  elif (pList1[0] == Conn.AND and pList2[0] == Conn.AND) or (pList1[0] == Conn.OR and pList2[0] == Conn.OR):
    ## check length
    if len(pList1) == len(pList2):
      combined = []
      ## create combined list with unique clauses
      for item1 in pList1[1:]:
        if not item1 in combined:
          combined.append(item1)
      for item2 in pList2[1:]:
        if not item2 in combined:
          combined.append(item2)
      # if length of combined senetence if equal to original, then same
      if len(combined) == len(pList1[1:]):
        return True
      else:
        return False
    else:
      return False
  else:
    return False

def removeDups(pList):
  ##return literals
  if type(pList) == str:
    return pList
  elif pList[0] == Conn.NOT:
    return pList
  elif pList[0] == Conn.AND or pList[0] == Conn.OR:
    ## if root is OR/AND, remove duplicates of childs recursively
    childsNoDups = map(removeDups, pList[1:])
    childs = [childsNoDups[0]]
    ## put unique childs in childs list
    for i in range(1, len(childsNoDups)):
      item = childsNoDups[i]
      present = False
      for otherItem in childs:
        if isSame(item, otherItem):
          #print "Same " + str(item) +  " ...... " + str(otherItem) 
          present = True
          break;
      if not present:
        childs.append(item)
    ## handle cases like [and A A] => A
    if len(childs) == 1:
      return childs[0]
    else:
      return [pList[0]] + childs



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

def CNFconverterMain(argv):
  parser = argparse.ArgumentParser()
  ## add required argument -i
  parser.add_argument('-i', dest='inputfilename', required = True)
  args = parser.parse_args(argv)
  infname = args.inputfilename

  ## open input file and read lines
  infile = open(infname, "r")
  indata = infile.readlines()

  ## open output file
  outfile = open("sentences_CNF.txt", "w")
  numLines = int(indata[0])
  for i in range(1, numLines+1):
    pSentence = indata[i]
    #print "\n"
    #print "Sentence: " + str(i)
    #print "Original: " + pSentence
    #print "Original:" + toSymbolString(eval(pSentence))
    try:
      list_biCond_elim = eliminateIff(eval(pSentence))
    #print "Iff elim: " + str(list_biCond_elim)
    #print "Iff elim: " + toSymbolString(list_biCond_elim)

      list_impl_elim = eliminateImplies(list_biCond_elim)
    #print "Implies elim: " + str(list_impl_elim)
    #print "Implies elim: " + toSymbolString(list_impl_elim)

      list_neg_down = pushNegDown(list_impl_elim)
    #print "Neg Down: " + str(list_neg_down)
    #print "Neg Down: " + toSymbolString(list_neg_down)

      list_distr = distribute(list_neg_down)
    #print "Distr: " + str(list_distr)
    #print "Distr: " + toSymbolString(list_distr)

      list_remove_dups = removeDups(list_distr)
    #print "removeDups: " + str(list_remove_dups)
    #print "removeDups: " + toSymbolString(list_remove_dups)

    except:
      outfile.write("\n")
    else:
    ## write the result to output file
      if type(list_remove_dups) == str:
        outfile.write("'" + str(list_remove_dups) + "'")
      else:
        outfile.write(str(list_remove_dups))
      if not i == numLines:
        outfile.write("\n")
  infile.close()
  outfile.close()

if __name__=="__main__":
  CNFconverterMain(sys.argv[1:])