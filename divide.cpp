#include <iostream>
#include <fstream>
#include <string>
using namespace std;

#define NAMESIZE 64

int divide(const char* rfilename,const char*wfilename,int pos){
  //一つのSwarmを分解
  ifstream ifs(rfilename);
  ofstream ofs(wfilename);
  string buf="";
  ifs.seekg(pos);
  while(getline(ifs,buf)){
    ofs << buf << endl;
    if(buf.size() == 1){
      break;
    }
  }

  return ifs.tellg();
}
int main(int argc,char *argv[]){
  int cur_position=0;
  int i=1;
  char out_name[NAMESIZE];
  while(cur_position >= 0){
    sprintf(out_name,"Swarm%d",i++);
    cur_position =divide(argv[1],out_name,cur_position);
  }

  return 0;
}
