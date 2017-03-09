#!/usr/bin/python
import sys, argparse, re


def arg_parser():
  parser = argparse.ArgumentParser(description='Eliminate sparse domains from a Flatzinc model') 
  parser.add_argument('infile', metavar='F', type=str, nargs='?',
    help='input Flatzinc model')
  return parser

def desparse(infile):
  regex = re.compile(r"""var \{([0-9 ,]+)\}: ([a-zA-Z0-9_]+) *[:;]""")
  for line in infile.readlines():
    match = re.match(regex, line)
    if match:
      vals = map(lambda v : int(v.strip()),  match.group(1).split(','))
      ident = match.group(2)
      print "var {0}..{1}: {2};".format(min(vals), max(vals), ident)
    else:
      print line.strip()
      
if __name__ == '__main__':
  parser = arg_parser()
  args = parser.parse_args()
  
  if args.infile:
    infile = open(args.infile)
    desparse(infile)
    infile.close()
  else:
    desparse(sys.stdin)
