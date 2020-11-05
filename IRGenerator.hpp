/*
    * Abstract Syntax Tree as input
    * Convert to 3 Address Code incrementally
    * File generated is a.ir
*/

#include <bits/stdc++.h>
#include "treeNode.hpp"
#include "symbolTable.hpp"
#include "codeGenerator.hpp"

using namespace std;

long long int label_count = 1ll;
long long int temp_count = 1ll;
list<int> lns;
set<string> all_vars;
set<string> used_vars;
extern treeNode* ast;
int prev_line;
vector<string> decl_list;
map<string, int> decl_order;
map<int, int> shifts, folds;
set<int> fold_lines;
map<int, vector<pair<string,int>> > props;
int ifb=-1;
ofstream IR;        // file containing IR
ofstream SUM;

symbolTableStack env;    // current symbol table environment
symbolTable final_table, tmp1;    // used for code generation

int table_offset = 0;
int table_arg_offset = 0;
int depth_counter = 0;



bool isPowerOfTwo (int x)
{
  return x && (!(x&(x-1)));
}
void printAST(treeNode* root, string prefix = "", bool isLast = true) {
    if(root == NULL) {
        return;
    }
    cout << prefix;
    if(isLast) {
        cout << "└───────";
    }
    else {
        cout << "├───────";
    }
    if(root->nodeName == "identifier") {
        cout << root->lexValue << endl;
    }
    else {
        cout << root->nodeName << endl;
    }
    for(int i = 0; i < root->children.size(); i++) {
        if(i == root->children.size() - 1) {
            printAST(root->children[i], prefix + "|        ", true);
        }
        else {
            printAST(root->children[i], prefix + "|        ", false);
        }
    }
}

string newLabel() {   // returns new label
    string LABEL = ".L";
    string x = to_string(label_count);
    LABEL += x;
    label_count++;
    return LABEL;
}

string newTemp() {  // returns new temp variable for 3 address code
    string TEMP = "$t";
    string x = to_string(temp_count);
    TEMP += x;
    temp_count++;
    return TEMP; 
}

void setInherited(treeNode* root) {
    if(root->nodeName == "func_decl") {
        depth_counter = 0;
        root->depth = depth_counter;
        root->func_name = root->children[1]->lexValue;
    }
    if(root->nodeName == "compound_stmt") {
        depth_counter++;
        for(auto& child : root->children) {
            child->depth = depth_counter;
        }
    }
    else {
        for(auto& child : root->children) {
            child->depth = root->depth;
        }
    }
    for(auto& child : root->children) {
        child->func_name = root->func_name;
    }

}
bool gkn(string var){
    if(final_table.isInTable(var)) {
        auto node = final_table.getNode(var);
        return node->known;
    }
    else {
        return true;
    }
}
int gkl(string var){
	if(final_table.isInTable(var)) {
	    auto node = final_table.getNode(var);
	    return node->kill;
	}
	else
		return 0;
}
int gval(string var){
    if(final_table.isInTable(var)) {
        auto node = final_table.getNode(var);
        return node->value;
    }
    else {
        return stoi(var);
    }
}
bool inum(string var){
	if(final_table.isInTable(var)) 
        return false;
    else 
    	return true;
}
void skn(string var, bool fl){
    auto node = final_table.getNode(var);
    node->known=fl;
}
void sval(string var, int val){
    auto node = final_table.getNode(var);
    node->value=val;    
}
int inckl(string var){
    auto node = final_table.getNode(var);
    node->kill=node->kill+1;
}
void temptrav(treeNode* root) {
    // setInherited
    string name = root->nodeName;
    // cout<<name<<endl;
    if(name=="print_stmt" || name=="expr"){
        lns.pop_front();
    }
    for(auto& child : root->children) {
        temptrav(child);
    }
}
//a=b+c

class expnode{
public:
	string me;//result
	string l;
	string r;
	string op;
	int lno;
	int kl, kr;
	expnode(string me1, string l1,string r1, string op1, int lno1, int kl1, int kr1){
		me=me1;
		l=l1;
		r=r1;
		op=op1;
		lno=lno1;
		kl=kl1;
		kr=kr1;
	}
	void print(){
		cout<<me<<" "<<l<<" "<<r<<" "<<op<<" "<<lno<<" "<<kl<<" "<<kr<<endl;
	}
};

vector<class expnode> all_exps;

bool check(class expnode c1, class expnode c2){
	return ((c1.l==c2.l)&&(c1.r==c2.r)&&(c1.op==c2.op)&&(c1.kl==c2.kl)&&(c1.kr==c2.kr));
}
void traverseAST(treeNode* root) {
    /**
     * Preprocess the current node
     * var_decl
     * local_decl
     * func_decl
     * assign_stmt
     * printf_stmt
     * if_stmt
     * while_stmt
     * return_stmt
     * expr
     * Pexpr
    **/
    setInherited(root);
    string name = root->nodeName;
    if(name == "var_decl") {
        // cout << "I am at " << name << endl;
    }
    if(name == "local_decl") {
        // cout << "I am at " << name << endl;
        if(root->children.size() == 3) {    // non-array declaration
            for(auto& child : root->children) {
                traverseAST(child);
            }
            auto child1 = root->children[1];
            child1->width = root->children[0]->width;
            child1->symbolTableName = child1->lexValue + "_" + child1->func_name + "_" + to_string(child1->depth);
            child1->offset = table_offset;
            child1->known=true;
            child1->kill=0;
            table_offset += child1->width;
            all_vars.insert(child1->lexValue);
            decl_list.push_back(child1->lexValue);
            env.set(child1->lexValue, child1);
            final_table.set(child1->symbolTableName, child1);
        }    
        else {  // array declaration
            for(auto& child : root->children) {
                traverseAST(child);
            }        
            auto child1 = root->children[1];
            string arr_length = root->children[3]->children[0]->children[0]->lexValue;   // assuming that the length of the array is an integer_lit
            child1->width = 4 * to_integer(arr_length);
            child1->symbolTableName = child1->lexValue + "_" + child1->func_name + "_" + to_string(child1->depth);
            child1->offset = table_offset;
            table_offset += child1->width;
            env.set(child1->lexValue, child1);
            final_table.set(child1->symbolTableName, child1);
        }
    }
    else if(name == "func_decl") {
            // cout << "I am at " << name << endl;
            table_offset = 4;
            table_arg_offset = 16;
            symbolTable top;
            env.addTable(top);
            IR << root->children[1]->lexValue <<  ":" << endl;
            for(auto& child : root->children) {
                traverseAST(child);
            }
            root->offset = table_offset;
            final_table.set("@" + root->children[1]->lexValue, root);
            env.removeTop();
            IR << "end" << endl;  // function code finishes
            used_vars.insert(root->children[1]->lexValue);
    }
    else if(name == "param") {
         if(root->children.size() == 2) {    // non-array paramter
            for(auto& child : root->children) {
                traverseAST(child);
            }
            auto child1 = root->children[1];
            child1->width = root->children[0]->width;
            child1->symbolTableName = child1->lexValue + "_" + child1->func_name + "_" + to_string(child1->depth);
            child1->offset = table_arg_offset;
            child1->isArg = true;
            table_arg_offset += 8;
            env.set(child1->lexValue, child1);
            final_table.set(child1->symbolTableName, child1);
        }       
    }
    else if(name == "assign_stmt") {
        //    cout << "I am at " << name << endl;
        for(auto& child : root->children) {
               traverseAST(child);
        }
        auto op_child = root->children[0];
        if(op_child->children.size() == 2) {

            
            string var=env.get(op_child->children[0]->lexValue);
            string val=op_child->children[1]->addr;
            // cout<<var<<" "<<val<<endl;
            skn(var, gkn(val));
            sval(var, gval(val)); 
            used_vars.insert(op_child->children[0]->lexValue);
            // cout << root->code << endl;
            string code;
            inckl(var);
            // cout<<gkn(val)<<endl;
            if(!gkn(val)){
                code = env.get(op_child->children[0]->lexValue) + " = " + op_child->children[1]->addr;
            }
            else{
            	folds[prev_line]=max(folds[prev_line], gval(op_child->children[1]->addr));
            	// cout<<prev_line<<" "<<gval(op_child->children[1]->addr)<<endl;
            	// cout<<folds[prev_line]<<endl;
                code = env.get(op_child->children[0]->lexValue) + " = " + to_string(gval(op_child->children[1]->addr));
            }
            IR << code << endl;

         }
         else {          // array assignment to be handled
            string code = env.get(op_child->children[0]->lexValue) + "[" + op_child->children[2]->addr + "]" + " = " + op_child->children[4]->addr;
            IR << code << endl;
         }
    }
    else if(name == "compound_stmt") {
        symbolTable top;
        env.addTable(top);
        for(auto& child : root->children) {
            traverseAST(child);
        }
        env.removeTop();
    }
    else if(name == "print_stmt") {
        // cout << "I am at " << name << endl;
        for(auto& child : root->children) {
            traverseAST(child);
        }
        string arg = env.get(root->children[4]->lexValue);
        if(!gkn(arg))
            IR << "printf" << " " << arg << endl;
        else{
            IR << "print" << " " << gval(arg) << endl;
            props[lns.front()].push_back({root->children[4]->lexValue, gval(arg)});
        }
        prev_line=lns.front();
        lns.pop_front();
    }
    else if(name == "scan_stmt"){
    	for(auto& child : root->children) {
            traverseAST(child);
        }
        string arg = env.get(root->children[5]->lexValue);
        skn(arg, false);
        inckl(arg);    
        IR << "scanf" << " " << arg << endl;
        used_vars.insert(root->children[5]->lexValue);
    }
    else if(name == "if_stmt") {
    //    cout << "I am at " << name << endl;
        if(root->children.size() == 5) {   // if but no else
            string l1 = newLabel();
            traverseAST(root->children[2]);  // expression
            if(gkn(root->children[2]->addr))
            {
                if(gval(root->children[2]->addr))
                {
                    traverseAST(root->children[4]);
                    ifb=1;
                }
                else{
                    ifb=0;
                }
            }
            else
            {
	            string code3 = "ifFalse " + root->children[2]->addr + " goto " + l1; 
                IR << code3 << endl;
                traverseAST(root->children[4]);  // statement   
                string final_code = l1 + ":";
                IR << final_code << endl;    
            }
            
        }
        else {    // if followed by an else
            traverseAST(root->children[2]);  // expression
            string l1 = newLabel();
            string l2 = newLabel();
            if(gkn(root->children[2]->addr))
            {
                // SUM<<"IF "<<lns.front()<<endl;
                if(gval(root->children[2]->addr)){
                    traverseAST(root->children[4]);
                    temptrav(root->children[6]);
                    ifb=1;
                }
                else{
                    temptrav(root->children[4]);
                    traverseAST(root->children[6]);
                    ifb=0;
                }
            }
            else{
                string code4 = "ifFalse " + root->children[2]->addr + " goto " + l1;
                IR << code4 << endl;
                unordered_map<string, pair<int, bool>> mem;                
                for(auto u:final_table.table){
                    mem[u.first]={0,false};
                    mem[u.first].first=u.second->value;
                    mem[u.first].second=u.second->known;
                }
                traverseAST(root->children[4]);  // if statement
                for(auto u:mem){
                    final_table.table[u.first]->value=mem[u.first].first;
                    final_table.table[u.first]->known=mem[u.first].second;
                }
                string code5 = "goto " + l2 + "\n" + l1 + ":";
                IR << code5 << endl;
                traverseAST(root->children[6]);  // else statement
                string code6 = l2 + ":";
                IR << code6 << endl;    
            } 
        }
   }
   else if(name == "while_stmt") {
    //    cout << "I am at " << name << endl;
        string l1 = newLabel(); // start of the loop
        string code5 = l1 + ":";
        IR << code5 << endl;
        traverseAST(root->children[2]); // condition expression
        string l2 = newLabel(); // outside the loop
        string code3 = "ifFalse " + root->children[2]->addr + " goto " + l2;
        IR << code3 << endl;
        traverseAST(root->children[4]); // statement
        string code6 = "goto " + l1 + "\n" + l2 + ":";
        IR << code6 << endl;
   }
   else if(name == "return_stmt") {
     //    cout << "I am at " << name << endl;
        for(auto& child : root->children) {
            traverseAST(child);
        } 
        if(root->children.size() == 2) {
            IR << "return " << "0" << endl;
        }
        else {
            IR << "return " << root->children[1]->addr << endl;
        }
   }
   else if(name == "incr_stmt") {
        for(auto& child : root->children) {
           traverseAST(child);
        }
        string var = env.get(root->children[0]->lexValue);
        IR << var << " = " << var << " PLUS " << 1 << endl;
        sval(var, 1+gval(var)); 
        skn(var, gkn(var));//DONE
   }
   else if(name == "decr_stmt") {
       for(auto& child : root->children) {
           traverseAST(child);
       }
       string var = env.get(root->children[0]->lexValue);
       IR << var << " = " << var << " MINUS " << 1 << endl;
       sval(var, -1+gval(var)); 
       skn(var, gkn(var));//DONE
   }
   else if(name == "expr") {
        // cout << "I am at " << name << endl;
        if(root->children.size() == 1) {   // binary op or Pexpr
            string op = root->children[0]->nodeName;
            auto op_child = root->children[0];
            if(op_child->children.size() == 2) {     // binary op
                if(op == "AND") { //TODO
                    root->addr = newTemp();
                    op_child->symbolTableName = root->addr;
                    final_table.set(root->addr, op_child);
                    op_child->width = 4;
                    op_child->offset += table_offset;
                    table_offset += 4;
                    env.set(root->addr, op_child);
                    traverseAST(op_child->children[0]);
                    traverseAST(op_child->children[1]);
                    bool f1 =gkn(op_child->children[0]->addr);
                    bool f2 =gkn(op_child->children[1]->addr);
                    bool fl=f1&&f2;
                    int v1=gval(op_child->children[0]->addr);
                    int v2=gval(op_child->children[1]->addr);
                    bool fl1=inum(op_child->children[0]->addr)&&inum(op_child->children[1]->addr);
                    int kl1=gkl(op_child->children[0]->addr);
                    int kl2=gkl(op_child->children[1]->addr);
                    skn(root->addr, fl);

                    string c1, c2;
                    int vl;
                    if(!fl){
                    	if(f1)
                            c1 = to_string(gval(op_child->children[0]->addr));
                        else
                            c1 = op_child->children[0]->addr;

                        if(f2)
                            c2 = to_string(gval(op_child->children[1]->addr));
                        else
                            c2 = op_child->children[1]->addr;
                        
                        string L1 = newLabel();
                        string code1 = "ifFalse " + c1 + " goto " + L1;
                        IR << code1 << endl;
                        string L2 = newLabel();
                        string code2 = "if " + c2 + " goto " + L2;
                        IR << code2 << endl;
                        string L3 = newLabel();
                        IR << L1 << ":" << endl;
                        IR << root->addr << " = " << 0 << endl;
                        IR << "goto " << L3 << endl;
                        IR << L2 << ":" << endl;
                        IR << root->addr << " = " << 1 << endl;
                        IR << L3 << ":" << endl;


                        class expnode temp_exp(root->addr, op_child->children[0]->addr, op_child->children[1]->addr, op, lns.front(), kl1, kl2);
                        all_exps.push_back(temp_exp);
                    }
                    else{
                    	vl=v1&&v2;
                    	sval(root->addr, vl);
                        fold_lines.insert(lns.front());
                    }

                    
                }
                else if(op == "OR") {//TODO
                    root->addr = newTemp();
                    op_child->symbolTableName = root->addr;
                    final_table.set(root->addr, op_child);
                    op_child->width = 4;
                    op_child->offset += table_offset;
                    table_offset += 4;
                    env.set(root->addr, op_child);
                    
                    traverseAST(op_child->children[0]);
                    traverseAST(op_child->children[1]);
                    bool f1 =gkn(op_child->children[0]->addr);
                    bool f2 =gkn(op_child->children[1]->addr);
                    bool fl=f1&&f2;
                    int v1=gval(op_child->children[0]->addr);
                    int v2=gval(op_child->children[1]->addr);
                    bool fl1=inum(op_child->children[0]->addr)&&inum(op_child->children[1]->addr);
                    int kl1=gkl(op_child->children[0]->addr);
                    int kl2=gkl(op_child->children[1]->addr);
                    skn(root->addr, fl);
                    
                    string c1, c2;
                    int vl;
                    if(!fl){
                    	if(f1)
                            c1 = to_string(gval(op_child->children[0]->addr));
                        else
                            c1 = op_child->children[0]->addr;

                        if(f2)
                            c2 = to_string(gval(op_child->children[1]->addr));
                        else
                            c2 = op_child->children[1]->addr;

                        string L1 = newLabel();
                        string code1 = "if " + op_child->children[0]->addr + " goto " + L1;
                        IR << code1 << endl;
                        string L2 = newLabel();
                        string code2 = "ifFalse " + op_child->children[1]->addr + " goto " + L2;
                        IR << code2 << endl;
                        string L3 = newLabel();
                        IR << L1 << ":" << endl;
                        IR << root->addr << " = " << 1 << endl;
                        IR << "goto " << L3 << endl;
                        IR << L2 << ":" << endl;
                        IR << root->addr << " = " << 0 << endl;
                        IR << L3 << ":" << endl;
                        
                        class expnode temp_exp(root->addr, op_child->children[0]->addr, op_child->children[1]->addr, op, lns.front(), kl1, kl2);
                        all_exps.push_back(temp_exp);
                    }
                    else{
                    	vl=v1||v2;
                    	sval(root->addr, vl);
                        fold_lines.insert(lns.front());
                    }


                    
                }
                else {
                    for(auto& child : root->children) {
                       traverseAST(child);
                    }
                    root->addr = newTemp();
                    op_child->symbolTableName = root->addr;
                    final_table.set(root->addr, op_child);
                    op_child->width = 4;
                    op_child->offset += table_offset;
                    table_offset += 4;
                    env.set(root->addr, op_child);
                    bool f1 =gkn(op_child->children[0]->addr);
                    bool f2 =gkn(op_child->children[1]->addr);
                    bool fl=f1&&f2;
                    int v1=gval(op_child->children[0]->addr);
                    int v2=gval(op_child->children[1]->addr);
                    bool fl1=inum(op_child->children[0]->addr)&&inum(op_child->children[1]->addr);
                    int kl1=gkl(op_child->children[0]->addr);
                    int kl2=gkl(op_child->children[1]->addr);
                    // cout<<op_child->children[0]->addr<<" "<<op_child->children[1]->addr<<endl;
                    // cout<<kl1<<" "<<kl2<<endl;
                    skn(root->addr, fl);
                    if(!fl)
                    {
                        string code;
                        if(f1)
                        	folds[lns.front()]=max(folds[lns.front()], v1);
                        if(f2)
                        	folds[lns.front()]=max(folds[lns.front()], v2);
                        if(op=="MULT" && (f1 && isPowerOfTwo(v1)) )
                        {
                            
                            code = root->addr +  " = " + to_string((int)(log2(v1))) + " " + "EXP" + " " + op_child->children[1]->addr;
                            shifts[lns.front()]=max(shifts[lns.front()],  ((int)(log2(v1))));
                            class expnode temp_exp(root->addr, to_string((int)(log2(v1))), op_child->children[1]->addr, "EXP", lns.front(), 0, kl2);
                            all_exps.push_back(temp_exp);
                            // SUM<<"SHIFT "<<lns.front()<<" "<<to_string((int)(log2(v1)))<<endl;
                        }
                        else if(op=="MULT" && (f2 && isPowerOfTwo(v2))){
                            code = root->addr +  " = " + to_string((int)(log2(v2))) + " " + "EXP" + " " + op_child->children[0]->addr;
                            shifts[lns.front()]=max(shifts[lns.front()],  ((int)(log2(v2))));
                            class expnode temp_exp(root->addr, to_string((int)(log2(v2))), op_child->children[0]->addr, "EXP", lns.front(), 0, kl1);
                            all_exps.push_back(temp_exp);
                            // SUM<<"SHIFT "<<lns.front()<<" "<<to_string((int)(log2(v2)))<<endl;
                        }
                        else
                        {
                            if(f1)
                                code = root->addr +  " = " + to_string(gval(op_child->children[0]->addr)) + " " + op + " " + op_child->children[1]->addr;
                            else if(f2)
                                code = root->addr +  " = " + op_child->children[0]->addr + " " + op + " " + to_string(gval(op_child->children[1]->addr));
                            else
                                code = root->addr +  " = " + op_child->children[0]->addr + " " + op + " " + op_child->children[1]->addr;
                            class expnode temp_exp(root->addr, op_child->children[0]->addr, op_child->children[1]->addr, op, lns.front(), kl1, kl2);
                            all_exps.push_back(temp_exp);       
                        }
                        
                        
                        IR << code << endl;    
                    }    
                    else
                    {
                        int vl;
                        if(op=="PLUS")
                            vl=v1+v2;
                        if(op=="MINUS")
                            vl=v1-v2;
                        if(op=="MULT")
                            vl=v1*v2;
                        if(op=="DIV" && v2!=0)
                            vl=v1/v2;
                        if(op=="MOD" && v2!=0)
                            vl=v1%v2;
                        if(op=="LT")
                            vl=(v1<v2);
                        if(op=="GT")
                            vl=v1>v2;
                        if(op=="LEQ")
                            vl=v1<=v2;
                        if(op=="GEQ")
                            vl=v1>=v2;
                        if(op=="EQEQ")
                            vl=v1==v2;
                        if(op=="NEQ")
                            vl=v1!=v2;
                        sval(root->addr, vl);
                        fold_lines.insert(lns.front());
                        // folds[lns.front()]=max(folds[lns.front()], vl);
                    	// SUM<<"Fold "<<lns.front()<<endl;

                    }
                    // string final_code = code1 + code2 + code3 + "\n";
                }
            }
            else {          // Pexpr
                for(auto& child : root->children) {
                   traverseAST(child);
                }
                root->addr = root->children[0]->addr;
            }
        }
        else if(root->children.size() == 2) {   // unary op
            string op = root->children[0]->nodeName;
            root->addr = newTemp();
            root->children[0]->symbolTableName = root->addr;
            root->children[0]->width = 4;
            root->children[0]->offset += table_offset;
            table_offset += 4;
            env.set(root->addr, root->children[0]);
            final_table.set(root->addr, root->children[0]);
            for(auto& child : root->children) {
                traverseAST(child);
            }
            bool fl=gkn(root->children[1]->addr);
            cout<<fl<<endl;
            int v1=gval(root->children[1]->addr);
            bool fl1=inum(root->children[1]->addr);
            skn(root->addr, fl);
            if(!fl){
                string code = root->addr + " = " + op + " " + root->children[1]->addr;
                IR << code << endl;
            }        
            else{
                int vl;
                if(op=="PLUS")
                    vl=v1;
                if(op=="MINUS")
                    vl=-v1;
                if(op=="NOT")
                    vl=!v1;
                sval(root->addr, vl);  
                // cout<<vl<<endl;
                if(fl1){
                    fold_lines.insert(lns.front());	
                }
                // else{
                //     props[lns.front()].push_back({root->children[1]->lexValue, vl});
                // }
            }
            
        }
        else {
            // HANDLE sizeof, array reference, function call
            root->addr = newTemp();
            root->children[1]->symbolTableName = root->addr;
            root->children[1]->width = 4;
            root->children[1]->offset += table_offset;
            table_offset += 4;
            env.set(root->addr, root->children[1]);
            final_table.set(root->addr, root->children[1]);
            if(root->children[0]->nodeName == "SIZEOF") {
                for(auto& child : root->children) {
                    traverseAST(child);
                }
                string size;
                if(final_table.isInTable(root->children[2]->addr)) {
                    auto node = final_table.getNode(root->children[2]->addr);
                    size = to_string(node->width);
                }
                else {
                    size = "4";
                } 
                string code = root->addr + " = " + size;
                IR << code << endl;
            }
            else if(root->children[1]->nodeName == "[") {    // array expression
                for(auto& child : root->children) {
                    traverseAST(child);
                }
                string code = root->addr + " = " + env.get(root->children[0]->lexValue) + "[" + root->children[2]->addr + "]";
                IR << code << endl;
            } 
            else {     // function call
                for(auto& child : root->children) {
                    traverseAST(child);
                }
                stack<string> s = root->children[2]->arg_stack;
                int n = s.size();
                while(!s.empty()) {
                    string arg = s.top();
                    s.pop();
                    IR << "param " << arg << endl;
                }
                string code = root->addr + " = " + "call function " + root->children[0]->lexValue + " " + to_string(n);
                IR << code << endl;
             }
        }//DONE
        prev_line=lns.front();
        lns.pop_front();        
   }
   else if(name == "args") {
       for(auto& child : root->children) {
           traverseAST(child);
       }
       root->arg_stack = root->children[0]->arg_stack;
   }
   else if(name == "arg_list") {
       for(auto& child : root->children) {
            traverseAST(child);
       }
       if(root->children.size() == 1) {
            root->arg_stack.push(root->children[0]->addr);
       }
       else {
            stack<string> s = root->children[0]->arg_stack;
            s.push(root->children[2]->addr); 
            root->arg_stack = s;
       }
   }
   else if(name == "Pexpr") {
        // cout << "I am at " << name << endl;
        if(root->children.size() == 3) {   // (expr)
            for(auto& child : root->children) {
                traverseAST(child);
            }
            root->addr = root->children[1]->addr;
            root->code = root->children[1]->code;
            root->known = root->children[1]->known;
            root->value = root->children[1]->value;
        }
        else {
            if(root->children[0]->nodeName == "identifier") {
                root->addr = env.get(root->children[0]->lexValue);
                skn(root->addr, gkn(env.get(root->children[0]->lexValue)));
                sval(root->addr, gval(env.get(root->children[0]->lexValue)));
                if(gkn(root->addr)){
                    props[lns.front()].push_back({root->children[0]->lexValue, gval(env.get(root->children[0]->lexValue))});
                    // props.push_back({lns.front(), });
                    // SUM<<"Prop "<<lns.front()<<endl;
                }
            }
            else {
                root->addr = root->children[0]->lexValue;
                root->known = true;
                root->value=stoi(root->children[0]->lexValue);
            }
        }
   }
   if(name != "expr" and name != "Pexpr" and name != "assign_stmt" and name != "if_stmt" and name != "while_stmt" and name != "func_decl" and name != "compound_stmt" and 
   name != "print_stmt" and name != "param" and name != "args" and name != "arg_list" and name != "return_stmt" and name != "incr_stmt" and name != "decr_stmt" and name!="scan_stmt") {
        string final_code = "";
        for(auto& child : root->children) {
            traverseAST(child);
            // final_code += child->code;
        }
        // root->code = final_code;
   }
}
bool comp1(string s1,string s2){
	return decl_order[s1]<decl_order[s2];
}
bool comp2(pair<string, int> s1, pair<string, int> s2){
	return decl_order[s1.first]<decl_order[s2.first];
}
int generateIR(std::list<int>& lines, int lnif) 
{
    // printAST(ast, "", true);
    for(auto u:lines)
    	folds[u]=INT_MIN;
    lns=lines;
    IR.open("a.ir");
    traverseAST(ast);
    // cout << "-----------3AC---------" << endl;
    IR.close();
    SUM.open("summary.txt");
    
    int cn=0;
    for(auto u:decl_list)
    {
    	decl_order[u]=cn++;
    }
    std::vector<string> temp;
    

    ////////////////////////////////////////////////////////////////////////////////////////

    SUM<<"unused-vars\n";
    for(auto u:all_vars){
        if(used_vars.count(u)==0)
            temp.push_back(u);
    }
    sort(temp.begin(), temp.end(), comp1);
    for(auto u:temp)
    	SUM<<u<<endl;
    SUM<<endl;


    ////////////////////////////////////////////////////////////////////////////////////////


    SUM<<"if-simpl"<<endl;
    if(ifb!=-1)
    	SUM<<ifb<<endl;
    SUM<<endl;
    
    ////////////////////////////////////////////////////////////////////////////////////////

    SUM<<"strength-reduction"<<endl;
    for(auto u:shifts)
        SUM<<u.first<<" "<<u.second<<endl;
    SUM<<endl;

    ////////////////////////////////////////////////////////////////////////////////////////


    SUM<<"constant-folding"<<endl;
    for(auto u:fold_lines) if(u!=lnif)
        SUM<<u<<" "<<folds[u]<<endl;  
    SUM<<endl;
    

    ////////////////////////////////////////////////////////////////////////////////////////


    SUM<<"constant-propagation"<<endl;
    for(auto u:props)
        sort(props[u.first].begin(), props[u.first].end(), comp2);
    for(auto u:props) if(u.first!=lnif){
        SUM<<u.first<<" ";
        set<string> done;
        for(auto v:props[u.first])
        	if(done.count(v.first)==0){
	            SUM<<v.first<<" "<<v.second<<" ";
	            done.insert(v.first);
        	}
        SUM<<endl;
    }
    SUM<<endl;
    

    ////////////////////////////////////////////////////////////////////////////////////////

    SUM<<"cse"<<endl;
    int n=all_exps.size();
    int vis[n];
    memset(vis, 0, sizeof(vis));
    map<string, string> confs;
    set<string> dels;
    for(int i=0; i<n; i++){
    	std::vector<int> lnos;
    	lnos.push_back(all_exps[i].lno);
    	for(int j=i+1; j<n; j++){
    		if(check(all_exps[i], all_exps[j]) && vis[j]==0){
    			lnos.push_back(all_exps[j].lno);
    			confs[all_exps[j].me]=all_exps[i].me;
    			dels.insert(all_exps[j].me);
    			vis[j]=1;
    			for(int k=j+1; k<n; k++){
    				if(vis[k]==0){
    					if(all_exps[j].me==all_exps[k].l)
    						all_exps[k].l=all_exps[i].me;
    					if(all_exps[j].me==all_exps[k].r)
    						all_exps[k].r=all_exps[i].me;
    				}
    			}
    		}
    	}
    	if(lnos.size()>1){
    		for(auto u:lnos)
	    		SUM<<u<<" ";
	    	SUM<<endl;	
    	} 
	    	
    }
    SUM<<endl;
    SUM.close();
    // final_table.debug();  // final symbol table
    codeGenerator(confs, dels);    // generate x86 code
    return 0;
}


//t5->t3
//t6->t4

//t3=a+5
//t4=t3+b
//t6=t3+b  //mark
//t7=t4+1