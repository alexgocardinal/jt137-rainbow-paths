// Independent RUP checker; retains deleted, previously justified clauses.
// A clause is accepted only if its negation unit-propagates to contradiction.
#include <algorithm>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
struct Checker {
 int nv; vector<vector<int>> clauses, watch; vector<int> units;
 bool empty=false;
 explicit Checker(int n):nv(n),watch(2*n){}
 int ix(int lit){return 2*(abs(lit)-1)+(lit<0);}
 void add(vector<int> c){
  sort(c.begin(),c.end());c.erase(unique(c.begin(),c.end()),c.end());
  for(int l:c)if(l==0||abs(l)>nv)throw runtime_error("literal out of range");
  int id=clauses.size();clauses.push_back(c);
  if(c.empty())empty=true;
  else if(c.size()==1)units.push_back(c[0]);
  else {watch[ix(c[0])].push_back(id);watch[ix(c[1])].push_back(id);}
 }
 bool rup(const vector<int>& proposed){
  if(empty)return true;
  vector<signed char> val(nv+1,0);vector<int> queue;
  auto setlit=[&](int l){int v=abs(l),s=l>0?1:-1;if(val[v]==-s)return false;if(!val[v]){val[v]=s;queue.push_back(l);}return true;};
  for(int l:units)if(!setlit(l))return true;
  for(int l:proposed)if(!setlit(-l))return true;
  size_t head=0;
  while(head<queue.size()){
   int falsified=-queue[head++];auto &ids=watch[ix(falsified)];size_t j=0;
   while(j<ids.size()){
    int id=ids[j];auto &c=clauses[id];
    if(c[0]==falsified)swap(c[0],c[1]);
    if(c[1]!=falsified)throw runtime_error("watch invariant failed");
    int other=c[0];if(val[abs(other)]==(other>0?1:-1)){j++;continue;}
    bool moved=false;
    for(size_t q=2;q<c.size();q++)if(val[abs(c[q])]!=(c[q]>0?-1:1)){
     int replacement=c[q];swap(c[1],c[q]);
     watch[ix(replacement)].push_back(id);ids[j]=ids.back();ids.pop_back();moved=true;break;
    }
    if(moved)continue;
    if(!setlit(other))return true;
    j++;
   }
  }
  return false;
 }
};
int main(int argc,char** argv){
 try{
  if(argc!=3)throw runtime_error("usage: checker CNF PROOF");
  ifstream cnf(argv[1]);if(!cnf)throw runtime_error("missing CNF");
  string line;int nv=-1,nc=-1;vector<vector<int>> initial;vector<int> partial;
  while(getline(cnf,line)){
   if(line.empty()||line[0]=='c')continue;
   if(line[0]=='p'){string p,fmt;istringstream s(line);s>>p>>fmt>>nv>>nc;if(fmt!="cnf"||nv<0)throw runtime_error("bad header");continue;}
   istringstream s(line);int x;while(s>>x){if(x)partial.push_back(x);else {initial.push_back(partial);partial.clear();}}
  }
  if(nv<0||!partial.empty()||int(initial.size())!=nc)throw runtime_error("CNF parse error");
  Checker check(nv);for(auto c:initial)check.add(c);
  ifstream proof(argv[2]);if(!proof)throw runtime_error("missing proof");
  long long additions=0,deletions=0,line_number=0;bool derived_empty=false;
  while(getline(proof,line)){
   line_number++;if(line.empty())continue;
   if(line[0]=='d'){deletions++;continue;}
   if(line[0]=='c')continue;
   istringstream s(line);int x;vector<int> c;bool ended=false;
   while(s>>x){if(!x){ended=true;break;}if(abs(x)>nv)throw runtime_error("proof literal out of range");c.push_back(x);}
   if(!ended)throw runtime_error("unterminated proof clause");
   if(!check.rup(c))throw runtime_error("not RUP at line "+to_string(line_number));
   check.add(c);additions++;if(c.empty())derived_empty=true;
  }
  if(!derived_empty)throw runtime_error("no derived empty clause");
  cout<<"PASS "<<additions<<" "<<deletions<<"\n";
 }catch(const exception &e){cerr<<e.what()<<"\n";return 1;}
}
