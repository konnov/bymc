#
# Generate rudimentary documentation for PyCUDD from the CUDD external header file and the pycudd module
#
# Bugs to : aravind@engineering.ucsb.edu
#

import pycudd
import re

# Global data structures
ref_dict = {}          # Dict indexed by CUDD func name --> list of "See Also" CUDD func names
rev_fn_dict = {}       # Dict indexed by CUDD func name --> PyCUDD func name 
pycudd_additions = {}  # Dict indexed by class name --> list of augmentations
pycudd_normal = {}     # Dict indexed by class name --> dict indexed by PyCUDD func name --> CUDD func name 

cfnc = open("cudd_funcs","r").readlines()
doc_file_name = "pycudd_doc.html"
doc_file = open(doc_file_name,"w")
classes_to_doc = ["DdNode","DdManager","DdArray","IntArray","StringArray","DoubleArray","DdGen","DdTlcInfo","NodePair","EpDouble"]

# Read in the list of "See Also" functions for each CUDD function and store it in the global ref_dict
def read_cudd_see_alsos():
    fnstr = r'.*name="(\w*)".*'
    func_name = re.compile(fnstr)
    see_str = r'.*">(\w*)</a>.*'
    see_re = re.compile(see_str)
    cudd_doc = open("cuddAllDet.html","r")
    line = cudd_doc.readline()
    in_see_also = 0
    fname = ''
    while line != '':
        mt = func_name.match(line.strip(),0)
        if mt:
            fname = mt.groups()[0].strip()
            ref_dict[fname] = []
        if "See Also" in line: in_see_also = 1
        if in_see_also:
            mtn = see_re.match(line.strip(),0)
            if mtn:
                ref_dict[fname].append(mtn.groups()[0].strip())
        if line.strip() == r'<\code>':
            in_see_also = 0
        line = cudd_doc.readline()
    cudd_doc.close()

# Given a class, try and determine who is from CUDD and who was added
# Use that to populate pycudd_normal and pycudd_additions respectively
# Additionally, populate the global reverse look-up dictionary rev_fn_dict
def create_reverse_lookups_and_additions(class_dict,cname):
    not_there = []
    fn_dict = {}
    for fname,fn in class_dict.items():
        trial1 = 'Cudd_'+fname
        trial2 = 'Cudd_bdd'+fname
        trial3 = 'cudd'+fname
        there = False
        for x in cfnc:
            if trial1 == x.strip() or trial2 == x.strip() or trial3 == x.strip():
                fn_dict[fname] = x.strip()
                rev_fn_dict[x.strip()] = fname 
                there = True
                break
        if not there:
            not_there.append(fname)
    pycudd_additions[cname] = not_there
    pycudd_normal[cname] = fn_dict

# Given a doc-string that describes the function calling convention, get the args and ret-val
def get_args_and_ret_val(doc_str):
    funcargs = re.compile(r".*[(](.*)[)].*")
    funcret = re.compile(r".*->(.*)")
    fndocstr = doc_str.replace("\n"," ").strip()
    try:
        fret = funcret.match(fndocstr).groups()[0].strip()
    except:
        fret = ""
    fargs = funcargs.match(fndocstr).groups()[0].strip()
    nfargs = ""
    ret_tuple = False
    for sarg in fargs.split(','):
        if sarg.strip() == "self":
            nfargs += "self, "
            continue
        # Convention is that all arguments beginning with dum are actually SWIG-typemapped to return stuff, so ignore them
        if not sarg.split()[1].strip().startswith("dum_"):
            nfargs += sarg.strip()+", "
        else:  # This gets returned, so add to the output tuple
            typ = sarg.split()[0]
            nam = sarg.split()[1][4:]
            if len(fret):
                fret += ", %s %s" % (typ,nam)
            else:
                fret += "%s %s" % (typ,nam)
            ret_tuple = True
    if ret_tuple: # multiple args, so enclose in a tuple symbol
        fret = "(%s) " % fret
    nfargs = nfargs.strip().strip(',')
    fargs = nfargs
    #fargs = fargs[4:].strip(',') # Remove the self and the , if multiple args
    return fargs,fret

# Given the class dictionary and class name, generate the documentation for all
# the functions provided as class methods
def write_class_details(class_dict,cname):    
    not_there = pycudd_additions[cname]
    fn_dict = pycudd_normal[cname]
    fnames = class_dict.keys()
    fnames.sort()
    for fname in fnames:
        fn = class_dict[fname]
        if fname in fn_dict:
            cfname = fn_dict[fname]
            out_strs = []
            fargs, fret = get_args_and_ret_val(fn.__doc__)
            see_str = r"<tr><td>See Also</td><td>"
            for sstr in ref_dict[cfname]:
                if sstr in rev_fn_dict:
                    see_str += r'<a href="'+doc_file_name+'#'+rev_fn_dict[sstr]+r'">'+sstr+r'</a>'+"\n"
            out_strs = [ r'<a name="'+fname+r'">'+r'<a href="cuddAllDet.html#'+cfname+r'">'+cfname+r'</a><br>',
                         r'<table>',
                         r'<tr><td>Method of</td><td>'+'<a href="'+doc_file_name+'#'+cname+r'">'+cname+r'</a>'+r'</td></tr>',
                         r'<tr><td>Prototype</td><td>'+fret+' <b>'+fname+r'</b> ('+fargs+r')</td></tr>'+"\n",
                         see_str+r'</td></tr></table>',
                         r'<hr align="left" width="10%" />'+"\n"]
            for out_str in out_strs:
                doc_file.write(out_str+"\n")

    # Now output the augmented stuff 
    doc_file.write(r'<b><a name="'+cname+r'new">Additions to '+cname+' in PyCUDD</b><br><br>'+"\n")
    doc_file.write(r'<table>')
    for fname in not_there:
        if not fname.startswith("__"):
            fn = class_dict[fname]
            try:
                fargs, fret = get_args_and_ret_val(fn.__doc__)
                doc_file.write(r'<tr><td><a name="'+fname+r'">'+fname+r'</td><td>'+fret+' <b>'+fname+r'</b> ('+fargs+r')</td></tr>'+"\n")
            except:
                pass
            
    doc_file.write(r'</table>')
            
class_info_loc = r'<a href="'+doc_file_name+r'#%s"><h3>%s</h3></a>'
header = [
    r'<html>',
    r'<head><title>PyCUDD package documentation </title></head>',
    r'<body>',
    r'<h1>PyCUDD package documentation</h1>',
    r'<h2>Classes/Methods provided</h2>',
    r'<hr>']
header += map(lambda c: class_info_loc % (c,c), classes_to_doc)
header += [
    r'The document shows, for a given CUDD function, the corresponding PyCUDD class and method that implements it. The link highlighted in the CUDD name opens the',
    r' CUDD documentation for the function. The links in the See Also: section point to the corresponding PyCUDD function details. Refer to the file UNIMPLEMENTED for a list of',
    r'CUDD functions that are either redundant/unnecessary now/not yet wrapped. Some CUDD functions return values as side-effects to pointer parameters. In such cases, the PyCUDD return',
    r'value is a tuple consisting of the original return value, followed by any side-effect return values.'
    r'<hr>'
]

class_info_header = [
    r'<a name="%s"><h3>%s</h3></a>',
    r'<a href="'+doc_file_name+'#%snew'+r'">Additions</a> in PyCUDD<br><br>',
    r'<b>CUDD function mapping%s</b><br><br>'
]

trailer=[r'</html>']

read_cudd_see_alsos()

for line in header:
    doc_file.write(line+"\n")

for cls in classes_to_doc:
    create_reverse_lookups_and_additions(pycudd.__dict__[cls].__dict__,cls)
    
for cls in classes_to_doc:
    # Format the class header lines. Note the dummy %s in the last line for compatibility with %
    class_hdr_lines = map(lambda x: class_info_header[x[0]] % x[1], zip(range(3),[(cls,cls),cls,""]))
    # Gak! Ugliness. The class documentation is tacked on to the __del__ method due to SWIG issues
    # Remember to e-mail swig-devel with the details.
    if pycudd.__dict__[cls].__doc__[:2] != "__":
        class_hdr_lines.insert(1,"<br><br>")
        class_hdr_lines.insert(1,pycudd.__dict__[cls].__doc__)
    for line in class_hdr_lines:
        doc_file.write(line)
    write_class_details(pycudd.__dict__[cls].__dict__,cls)
    doc_file.write("<hr>\n")
    
for line in trailer: doc_file.write(line+"\n")

doc_file.close()
