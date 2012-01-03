#include <iostream>
#include <string>
#include <map>
#include <cstdlib>
#include <ctime>
#include <fstream>
#include <algorithm>
#include <GLUT/glut.h>
#include <boost/regex.hpp>
#include <boost/foreach.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/graph_utility.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/property_map/property_map.hpp>
#include <boost/graph/properties.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/graph/graphviz.hpp>
#include <boost/graph/dijkstra_shortest_paths.hpp>
#include "stdafx.h"
#include <gsl/gsl_vector.h>
#include <gsl/gsl_matrix.h>
#include <gsl/gsl_math.h>
#include <gsl/gsl_eigen.h>
#include <gsl/gsl_sort_vector.h>
#include <gsl/gsl_blas.h>
#define _USE_MATH_DEFINES
#include <math.h>
//-------------------Graph関連のグローバル変数---------------------------//
using namespace boost;
using namespace std;

typedef adjacency_list<vecS,vecS,directedS,no_property,property<edge_weight_t,int> > Graph;
typedef graph_traits<Graph>::vertex_descriptor Vertex;
typedef pair<string,string> Edge; //読み込んだものを直接辺とする
typedef pair<int,int> gEdges;	//stringの辺をintにマップして格納する

typedef map<int,string> IntToVertex;  //頂点のインデクスから頂点の名前へのマップ
typedef map<string,int> VertexToInt;  //頂点の名前から対応するインデクスへのマップ
typedef map<string,int> VertexToDegree; //頂点名からdegreeを得るマップ

vector<Edge> lines;   //辺を格納(Graph用)
vector<int> weights;  //辺の重み
vector<string> points;   //頂点を格納
map<string,bool> isPeer;
VertexToInt vi;
IntToVertex iv;
VertexToDegree deg;  //各頂点のdegreeを格納するマップ
vector<gEdges> glines;//辺を格納(表示用)
map<pair<string,string>,string > way;  //it has route 



#define MAX_BUF (1024)
#define SPRING (0)
#define SPECTRAL (1)
#define CIRCLE (2)
#define MDS_MODE (3)
#define WINDOW_HEIGHT (750.0)
#define WINDOW_WIDTH (750.0)
#define INF (100000)
//#define DEBUG
int strategy = 0; //描画モデルの指定
int click_mode = 0;     //クリックした場合のモード指定
string swarmID;
//--------------------OpenGL(spring)関連のグローバル変数-------------------------//
#define RAD (0.02)  //頂点半径
typedef pair<double,double> Vec2;

int redisplay_index;
int locus;        //移動中の頂点を消すか消さないか	
int savepoint[2];
//グラフ描画のための座標クラス


//---------------------MDS関連のグローバル関数----------------------------------//
gsl_matrix	* dist;	// distance matrix
vector< Vec2 >	mds_coord;

class Circle_Coord{  //Peerを円周上に配置する為のクラス
public:
  vector<Vec2> coord;
  vector<Vec2> verosity;
  vector<int> adjacency[MAX_BUF];
  int start_id,target_id;
  map<int,string> degToVertex;
  map<string,int> vertexToFrame;
  int frame_num;
  void InitCoord(Graph g){
    this->start_id = -1;
    this->target_id = -1;
    typedef graph_traits<Graph>::vertex_iterator vertex_iter;
    pair<vertex_iter,vertex_iter> vp;
    map<int,string>::iterator ite;
    map<string,bool>::iterator is_ite;
	map<string,int>::iterator deg_ite;
	int countAS=0; //the number of AS count,and the circle frame number
    srand((unsigned)time(NULL));
	for(vp = vertices(g) ; vp.first != vp.second ; ++vp.first){
	  ite = iv.find(*vp.first);
	  is_ite = isPeer.find((*ite).second);
	  deg_ite = deg.find((*ite).second);
	  if(!(*is_ite).second){
		degToVertex.insert(make_pair((*deg_ite).second,(*deg_ite).first));
		countAS++;
	  }
	}
	this->frame_num = (countAS/10)+1;
	map<int,string>::iterator iv_deg = degToVertex.begin();
	for(unsigned int i = 0 ; i < degToVertex.size() ; i++,iv_deg++){
	  vertexToFrame.insert(make_pair((*iv_deg).second,frame_num-(i/10)));
	}
    for(vp = vertices(g) ; vp.first != vp.second ; ++vp.first){
      ite = iv.find(*vp.first);    //得られた頂点のstring名を得る
      is_ite = isPeer.find((*ite).second);  //string名を用いてそれがPeerかどうかを見る
      if((*is_ite).second){  //Peerだった場合円周上に配置
		double t = 2.0*M_PI*(double)rand()/RAND_MAX;
		coord.push_back(make_pair(0.75*cos(t),0.75*sin(t)));
		verosity.push_back(make_pair(0.0,0.0));
      }
      else{  //その他はランダム
		double t = 2.0*M_PI*(double)rand()/RAND_MAX;
		double interval = 0.75/((double)frame_num+1.0);
		deg_ite = vertexToFrame.find((*ite).second);
		double radius = interval*(double)(*deg_ite).second;
		coord.push_back(make_pair(radius*cos(t),radius*sin(t)));
		verosity.push_back(make_pair(0.0,0.0));
      }
    }
    graph_traits<Graph>::edge_iterator ei,ei_end;
    for(tie(ei,ei_end) = edges(g) ; ei != ei_end ; ++ei){
      adjacency[source(*ei,g)].push_back(target(*ei,g)); 
      adjacency[target(*ei,g)].push_back(source(*ei,g));
    }
  }
  void MoveEuler(double dt,Vec2 f,int id){
    map<int,string>::iterator ite = iv.find(id);
    map<string,bool>::iterator is_ite = isPeer.find((*ite).second);
    coord.at(id).first += dt*(verosity.at(id).first);
    coord.at(id).second += dt*(verosity.at(id).second);
    verosity.at(id).first += dt*(f.first);
    verosity.at(id).second += dt*(f.second);
  }
  Vec2 GetCentrifugalForce(int id){   //淵に拘束を計算する関数
    map<int,string>::iterator ite = iv.find(id);
    map<string,bool>::iterator is_ite = isPeer.find((*ite).second);
	map<string,int>::iterator deg_ite;
	  const double R = 100.0;  //遠心力の係数
	  if((*is_ite).second){ //Peerだったら
		double x = coord.at(id).first;
		double y = coord.at(id).second;
		double d = x*x + y*y;
		d = sqrt(d);  //中心からの距離
		double tx = (x*0.75)/d;
		double ty = (y*0.75)/d;
		return make_pair(R*(tx-x),R*(ty-y));
    }
	  else{ //Peerでなかったら
		deg_ite = this->vertexToFrame.find((*ite).second);  //This point frame number
		double interval = 0.75/((double)frame_num+1.0);
		double radius = interval*(double)(*deg_ite).second;
		double x = coord.at(id).first;
		double y = coord.at(id).second;
		double d = x*x + y*y;
		d = sqrt(d);
		double tx = (x*radius)/d;
		double ty = (y*radius)/d;
		return make_pair(R*(tx-x),R*(ty-y));
	  }
  }
  Vec2 GetSpringForce(int id){
    const double k = 0.01;
    const double l = 0.0001;
    double fx=0,fy=0;
    for(unsigned int i = 0 ; i < adjacency[id].size() ; ++i){
      double dx = coord.at(id).first - coord.at(adjacency[id].at(i)).first;
      double dy = coord.at(id).second - coord.at(adjacency[id].at(i)).second;
      double d2 = dx*dx + dy*dy;
      d2 = sqrt(d2);
      double cos = dx/d2;
      double sin = dy/d2;
      double dl = d2 - l;
      fx += -k*dl*cos;
      fy += -k*dl*sin;
    }
    return make_pair(fx,fy);
  }
  Vec2 GetReplusiveForce(int id){
    const double g = 0.01;
    double fx=0,fy=0;
    for(unsigned int i = 0 ; i < coord.size() ; i++){
      if(i != id){
		double dx = coord.at(id).first - coord.at(i).first;
		double dy = coord.at(id).second - coord.at(i).second;
		double d2 = dx*dx + dy*dy;
		double d = sqrt(d2);
		double cos = dx / d;
		double sin = dy / d;
		fx += (g/d2)*cos;
		fy += (g/d2)*sin;
      }
    }
    return make_pair(fx,fy);
  }
  Vec2 GetFrictionForce(int id){
    const double m = 30.0;
    double vx = verosity.at(id).first;
    double vy = verosity.at(id).second;
    return make_pair(-m*vx,-m*vy);
  }
  
  void MoveAll(){
    Vec2 spring_force,replusive_force,friction_force,centrifugal_force,f;
    for(unsigned int i = 0 ; i < coord.size() ; i++){
      const double dt = 0.01;
      spring_force = GetSpringForce(i);
      replusive_force = GetReplusiveForce(i);
      friction_force = GetFrictionForce(i);
      centrifugal_force = GetCentrifugalForce(i);
      f.first = spring_force.first + replusive_force.first + friction_force.first + centrifugal_force.first;
      f.second = spring_force.second + replusive_force.second + friction_force.second + centrifugal_force.second;
      MoveEuler(dt,f,i);
    }
  }
  void printProperty(int id){
    map<int,string>::iterator ite;
    ite = iv.find(id);
    cout << "--------------------------" << endl;
    cout << (*ite).second << endl;
    cout << "x " << coord.at(id).first << " y " << coord.at(id).second << endl;
    cout << "vx " << coord.at(id).first << " vy " << coord.at(id).second << endl;
    for(int i = 0 ; i < adjacency[id].size() ; i++){
      ite = iv.find(adjacency[id].at(i));
      cout << (*ite).second << " ";
    }
    cout << endl;
  }
}Circle_Cd;

//drawing class for spring model
class Coord{
public:
  vector<Vec2> coord;    //座標をdoubleで格納する
  vector<Vec2> verosity; //速度をdoubleで格納する
  vector<int> adjacency[MAX_BUF];
  int start_id,target_id;
  void InitCoord(Graph g){
    this->start_id = -1;
    this->target_id = -1;
    typedef graph_traits<Graph>::vertex_iterator vertex_iter;
    pair<vertex_iter,vertex_iter> vp;
    map<int,string>::iterator ite;
    srand((unsigned)time(NULL));
    for(vp = vertices(g) ; vp.first != vp.second ; ++vp.first){
      ite = iv.find(*vp.first);
      coord.push_back(make_pair(((double)rand()/RAND_MAX)*2.0-1.0,((double)rand()/RAND_MAX)*2.0-1.0));
      verosity.push_back(make_pair(0.0,0.0));
    }
    graph_traits<Graph>::edge_iterator ei,ei_end;
    for(tie(ei,ei_end) = edges(g) ; ei != ei_end ; ++ei){
      adjacency[source(*ei,g)].push_back(target(*ei,g)); 
      adjacency[target(*ei,g)].push_back(source(*ei,g));
    }
  }
  void MoveEuler(double dt,Vec2 f,int id){
    coord.at(id).first += dt*(verosity.at(id).first);
    coord.at(id).second += dt*(verosity.at(id).second);
    verosity.at(id).first += dt*(f.first);
    verosity.at(id).second += dt*(f.second);
  }
  Vec2 GetSpringForce(int id){
    const double k = 0.1;
    const double l = 0.0001;
    double fx=0,fy=0;
    for(unsigned int i = 0 ; i < adjacency[id].size() ; ++i){
      double dx = coord.at(id).first - coord.at(adjacency[id].at(i)).first;
      double dy = coord.at(id).second - coord.at(adjacency[id].at(i)).second;
      double d2 = dx*dx + dy*dy;
      d2 = sqrt(d2);
      double cos = dx/d2;
      double sin = dy/d2;
      double dl = d2 - l;
      fx += -k*dl*cos;
      fy += -k*dl*sin;
    }
    return make_pair(fx,fy);
  }
  Vec2 GetReplusiveForce(int id){
    const double g = 0.01;
    double fx=0,fy=0;
    for(unsigned int i = 0 ; i < coord.size() ; i++){
      if(i != id){
		double dx = coord.at(id).first - coord.at(i).first;
		double dy = coord.at(id).second - coord.at(i).second;
		double d2 = dx*dx + dy*dy;
		double d = sqrt(d2);
		double cos = dx / d;
		double sin = dy / d;
		fx += (g/d2)*cos;
		fy += (g/d2)*sin;
      }
    }
    return make_pair(fx,fy);
  }
  Vec2 GetFrictionForce(int id){
    const double m = 30.0;
    double vx = verosity.at(id).first;
    double vy = verosity.at(id).second;
    return make_pair(-m*vx,-m*vy);
  }
  
  void MoveAll(){
    Vec2 spring_force,replusive_force,friction_force,f;
    for(unsigned int i = 0 ; i < coord.size() ; i++){
      const double dt = 0.01;
      spring_force = GetSpringForce(i);
      replusive_force = GetReplusiveForce(i);
      friction_force = GetFrictionForce(i);
      f.first = spring_force.first + replusive_force.first + friction_force.first;
      f.second = spring_force.second + replusive_force.second + friction_force.second;
      MoveEuler(dt,f,i);
    }
  }
#ifdef DEBUG
  int printProperty(int id){
    map<int,string>::iterator ite;
    ite = iv.find(id);
    cout << "--------------------------" << endl;
    cout << (*ite).second << endl;
    cout << "x " << coord.at(id).first << " y " << coord.at(id).second << endl;
    cout << "vx " << coord.at(id).first << " vy " << coord.at(id).second << endl;
    for(int i = 0 ; i < adjacency[id].size() ; i++){
      ite = iv.find(adjacency[id].at(i));
      cout << (*ite).second << " ";
    }
    cout << "degree=" << adjacency[id].size() << endl; 
    return adjacency[id].size();
  }
#endif
}Cd;

//--------------------OpenGL(spectral)関連のグローバル変数-------------------------//

gsl_matrix *adj;//隣接行列
vector<Vec2> spectral_coord;


//calculate edge cost between Peer and Peer（hop）
int count_distance(string buf){
  int d = 0;
  for(unsigned int i = 0 ; i < buf.size() ; i++){
    if(buf.at(i) == ' ' || buf.at(i) == '\t'){
      d++;
    }
  }
  return d-1;
}

//read from Swarm file
int reg_analyze(const char *filename){ 
  ifstream ifs(filename);
  string buf;
  getline(ifs,swarmID);
  cout << swarmID << endl;
  regex e("([0-9]+)( |\t)"); //エッジを抽出する正規表現
  regex s("^([0-9]+)");      //開始点を抽出する正規表現
  regex t("([0-9]+)\t$");    //終点を抽出する正規表現
  smatch start_result,end_result,edge_result;
  string v1,v2;
  string sink,tank;   //start Peer and target Peer
  while(getline(ifs,buf)){
	int flag = 0; //一つの行の何個目のpeerまたはASを見ているか
	string::const_iterator start = buf.begin();
	  string::const_iterator end = buf.end();
	  if(regex_search(start,end,start_result,s)){
	    isPeer.insert(make_pair(start_result.str(1),true));
	  }
	  if(regex_search(start,end,end_result,t)){
	    isPeer.insert(make_pair(end_result.str(1),true));
	  }
	  while(regex_search(start,end,edge_result,e)){
	    if(flag == 0){
	      v1 = edge_result.str(1);
	      sink = v1;
	      flag++;
	      start = edge_result[0].second;
	    }
	    else{
	      v2 = edge_result.str(1);
	      lines.push_back(make_pair(v1,v2));
	      lines.push_back(make_pair(v2,v1));
	      points.push_back(v1);
	      points.push_back(v2);
#ifdef DEBUG
	      cout << "v1 " << v1 << " v2 " << v2 << endl; 
#endif
	      v1 = v2;
	      flag++;
	      start = edge_result[0].second;
	    }
	  }
	  tank = v1;
	  way.insert(make_pair(make_pair(sink,tank),buf));
	  buf = "";
  }
  for(unsigned int i = 0 ; i < lines.size() ; i++){
	weights.push_back(1);
  }
  sort(points);
  points.erase(unique(points.begin(),points.end()),points.end());
  ifs.close();
  return points.size();
}

void MapInit(VertexToInt &vi,IntToVertex &iv){
  for(unsigned int i = 0 ; i < points.size() ; i++){
		vi.insert(make_pair(points.at(i),i));
  }
  for(unsigned int i = 0 ; i < points.size() ; i++){
	iv.insert(make_pair(i,points.at(i)));
  }
}

void LinesInit(VertexToInt &vi,vector<gEdges> &glines){
  map<string,int>::iterator ite1,ite2;
  for(unsigned int i = 0 ; i < lines.size() ; i++){
	ite1 = vi.find(lines.at(i).first);
	ite2 = vi.find(lines.at(i).second);
	glines.push_back(make_pair((*ite1).second,(*ite2).second));
  }
}

void InitDeg(const char *filename){
  ifstream ifs(filename);
  string buf;
  regex ver("^([0-9]+)");
  regex degree("([0-9]+)$");
  smatch ver_result,degree_result;
  string v;
  int d;
  while(getline(ifs,buf)){
    string::const_iterator start = buf.begin();
    string::const_iterator end = buf.end();
    if(regex_search(start,end,ver_result,ver)){
      v = ver_result.str(1);
    }
    if(regex_search(start,end,degree_result,degree)){
      d = atoi(degree_result.str(1).c_str());
    }
    deg.insert(make_pair(v,d));
  }
  ifs.close();
}

//drawing circle
void circle(double radius,double x,double y){
  double step = 2*M_PI/30.0;
  glBegin(GL_POLYGON);
  for(int i = 0 ; i < 30 ; i++){
    double t = step * (double)i;
    glVertex3d(x+radius*cos(t),y+radius*sin(t),0);
  }
  glEnd();
}

//drawing strings on windows
void drawString(const char *str,double x, double y,int size){
  void *font;
  if(size == 0){
	font = GLUT_BITMAP_HELVETICA_18;
  }
  else if(size == 1){
    font = GLUT_BITMAP_TIMES_ROMAN_10;
  }
  glRasterPos3f((float)x,(float)y,0.0);
  while(*str){
    glutBitmapCharacter(font,*str);
    ++str;
  }
}

//returning the course
vector<int> course(int s,int t){
  vector<int> cour;
  if(s < 0 || t < 0){
	cour.push_back(-1);
	return cour;
  }
  map<int,string>::iterator iv_ite_s = iv.find(s);
  map<int,string>::iterator iv_ite_t = iv.find(t);
  map<string,int>::iterator vi_ite;
  map<pair<string,string> , string>::iterator way_ite = way.find(make_pair((*iv_ite_s).second
									   ,(*iv_ite_t).second));
  string::const_iterator start,end;
  start = (*way_ite).second.begin();
  end = (*way_ite).second.end();
  regex v("([0-9]+)( |\t)");
  smatch edge_result;
  while(regex_search(start,end,edge_result,v)){
    vi_ite = vi.find(edge_result.str(1));
    cour.push_back((*vi_ite).second);
    start = edge_result[0].second;
  }
  return cour;
}

bool is_course(int v,vector<int> cour){
  for(unsigned int i = 0 ; i < cour.size() ; i++){
    if(v == cour.at(i)){
      return true;
    }
  }
  return false;
}


namespace metric{
    double cache[2];
    void set_chache( double x, double y){
        cache[0] = x;
        cache[1] = y;
    }
    double bary_center[2];
    bool is_bary_center_calculated = false;
    void calc_bary_center(){
        bary_center[0] = 0.; 
        bary_center[1] = 0.; 
		
        BOOST_FOREACH (Vec2 p, spectral_coord){
            bary_center[0] += p.first;
            bary_center[1] += p.second;
        }
        bary_center[0] = bary_center[0] / spectral_coord.size();
        bary_center[1] = bary_center[1] / spectral_coord.size();
		
        is_bary_center_calculated=true;
    }
    double dist_max(){
        double dm = 0;
        double d;
		
        BOOST_FOREACH (Vec2 p, spectral_coord){
            d = sqrt( (p.first - bary_center[0])*(p.first - bary_center[0])  + (p.second - bary_center[1])*(p.second - bary_center[1]));
            if (d > dm){
				dm = d;
            }
        }
        return dm;
    }
	
	
	
	
    double max;
    namespace loupe{
		
        // 恒等写像
        double identity(double domain){
            return domain;
        }
        // デバッグ用の関数 (1/2 に縮小するだけ)
        double half(double domain){
            return domain  /2.0;
        }
        // 放物線の虫眼鏡用関数
        double sqrt_transform(double domain){
            return sqrt(domain);
        }
        // 円弧の虫眼鏡用関数
        double arc(double domain){
            return sin(acos(domain -1));
        };
    }
	
    // この関数ポインタのアドレスを変えると，
    // 描画の拡大縮小に使われる関数が変わる．
    // 虫眼鏡の取り換えみたいなもの．
    //  (佐々木さんの元々のソースでは恒等写像(&loupe::identity))
    double (*measure)(double domain) = &loupe::sqrt_transform;
	
	
    double* rescale(double x, double y){
        double dist = sqrt(x*x + y*y);
        double scale = metric::measure(dist/max);
		
        double dir[2];
		dir[0] = x / sqrt(x*x + y*y);
		dir[1] = y / sqrt(x*x + y*y);
		
        x = dir[0] * scale * max;
        y = dir[1] * scale * max;
        set_chache(x, y);
        return cache;
    }
	
	
    // 上で measure として与えられた関数で空間を伸縮する.
    // glvertex2dv に引数として与えて使う
    double* scale(Vec2 coord){
        if (!is_bary_center_calculated){ calc_bary_center();max = dist_max();}
		
        double *pos=rescale(coord.first - bary_center[0], coord.second - bary_center[1]);
        pos[0] = pos[0] + bary_center[0];
        pos[1] = pos[1] + bary_center[1];
        return pos;
    }
}

//drawing verteces
void displayVertex(vector<Vec2> cor){
  vector<int> cour;
  for(unsigned int i = 0 ; i < cor.size() ; i++){
    map<int,string>::iterator ite = iv.find(i);
    map<string,bool>::iterator is_ite = isPeer.find((*ite).second);
    map<string,int>::iterator deg_ite;
    if((*is_ite).second){
      //if clicked, color is yellow
      if((i == Cd.start_id || i == Cd.target_id || i == Circle_Cd.start_id || i == Circle_Cd.target_id)
		 && (strategy == 0 || strategy == 2)){ 
		glColor3d(1.0,1.0,0.0);
      }
      else{
        //not clicked, color is green
		glColor3d(0.0,1.0,0.0);
      }
    }
    else{
      glColor3d(1.0,0.0,1.0);  //in case this is AS, color is pink
    }
	double vx,vy;
	if(strategy == 1){
	  double* scaled = metric::scale(cor.at(i));
	  vx = scaled[0];
	  vy = scaled[1];
	}
	else{
	  vx = cor.at(i).first;
	  vy = cor.at(i).second;
	}
    circle(RAD,vx,vy);
    const char* str = (*ite).second.c_str();
    glColor3d(1.0,0.0,0.0);
    drawString(str,vx,vy,0);
  }
}

//drawing edges(spring,circle)
void displayEdge(vector<Vec2> cor,vector<int> adj[],int size){
  glColor3d(0.5,0.5,0.5);
  vector<int> route;
  for(int i = 0 ; i < size ; i++){
    int start = i;
    for(unsigned int j = 0 ; j < adj[i].size() ; j++){
      int target = adj[i].at(j);
      glBegin(GL_LINES);
      glVertex2d(cor.at(start).first,cor.at(start).second);
      glVertex2d(cor.at(target).first,cor.at(target).second);
      glEnd();
    }
  }
  if(strategy == 0){
	route = course(Cd.start_id,Cd.target_id);
  }else if(strategy == 2){
	route = course(Circle_Cd.start_id,Circle_Cd.target_id);
  }
  if(route.at(0) >= 0){ //if the route is not void
	for(unsigned int i = 0 ; i < route.size()-1 ; i++){
	  int start = route.at(i);
	  int target = route.at(i+1);
	  glColor3d(1.0,1.0,0.0);
	  glBegin(GL_LINES);
	  glVertex2d(cor.at(start).first,cor.at(start).second);
	  glVertex2d(cor.at(target).first,cor.at(target).second);
	  glEnd();
	}
  }
}

//drawing edges(spectral,mds)
void displayEdge(vector<Vec2> cor){
  glColor3d(0.5,0.5,0.5);
  for(unsigned int i = 0 ; i < cor.size() ; i++){
    for(unsigned int j = 0 ; j < cor.size() ; j++){
      if(gsl_matrix_get(adj,i,j) != 0){
		glBegin(GL_LINES);
		if(strategy == 1){
		  glVertex2dv(metric::scale(cor.at(i)));
		  glVertex2dv(metric::scale(cor.at(j)));
		}
		else{
		  glVertex2d(cor.at(i).first,cor.at(i).second);
		  glVertex2d(cor.at(j).first,cor.at(j).second);
		}
		glEnd();
      }
    }
  }
}

void displaySwarmID(){
	glColor3d(0.0,0.0,0.6);
	drawString(::swarmID.c_str(),-0.95,-0.95,0.0);
}

//In Circle mode, drawing restrict circle
void displayCircleEdge(){
  double interval = 0.75/((double)Circle_Cd.frame_num+1.0);
  for(int i = Circle_Cd.frame_num+1 ; i > 0 ; i--){
	double radius = interval*((double)i);
	glColor3d(0.0,0.0,1.0);
	circle(radius,0.0,0.0);
	glColor3d(1.0,1.0,1.0);
	circle(radius-0.01,0.0,0.0);
  }
}

void display(){	
  int CdSize = points.size(); 
  int ave_x=0,ave_y=0;
  switch(strategy){
  case SPRING:
    //drawing in Spring model
    glClear(GL_COLOR_BUFFER_BIT);
    displayEdge(Cd.coord,Cd.adjacency,CdSize);
    displayVertex(Cd.coord);
	displaySwarmID();
    break;
  case SPECTRAL:
    //drawing in Spectral model
    glClear(GL_COLOR_BUFFER_BIT);
    displayEdge(spectral_coord);
    displayVertex(spectral_coord);
	displaySwarmID();
    break;
  case CIRCLE:
    //drawing in Circle mode
    glClear(GL_COLOR_BUFFER_BIT);
	displayCircleEdge();
    displayEdge(Circle_Cd.coord,Circle_Cd.adjacency,CdSize);
    displayVertex(Circle_Cd.coord);
    displaySwarmID();
    break;
  case MDS_MODE:
    //drawing in MDS mode
    glClear(GL_COLOR_BUFFER_BIT);
    displayEdge(mds_coord);    
    displayVertex(mds_coord);
	displaySwarmID();
    break;
  default:
    break;
  }
  glutSwapBuffers();
}
void init(){
	glClearColor(1.0,1.0,1.0,1.0);
}

void resize(int w,int h){
	glViewport(0,0,w,h);
	glLoadIdentity();
	glOrtho(-1.0,1.0,-1.0,1.0,-2.0,2.0);
}

//translate to regular coordinate
pair<double,double> regCoord(int x,int y){
  double vx = x / WINDOW_WIDTH;
  double vy = y / WINDOW_HEIGHT;
  return make_pair(vx*2.0-1.0,-(vy*2.0-1.0));
}

//returning whether vertex is pushed pr not
bool is_pushed(int id,double x,double y){
  double vx,vy;
  if(strategy == 0){
    vx = Cd.coord.at(id).first;
    vy = Cd.coord.at(id).second;
    if((x-vx)*(x-vx)+(y-vy)*(y-vy) < RAD*RAD){return true;}
    else{ return false;}
  }
  else if(strategy == 2){
    vx = Circle_Cd.coord.at(id).first;
    vy = Circle_Cd.coord.at(id).second;
    if((x-vx)*(x-vx)+(y-vy)*(y-vy) < RAD*RAD){return true;}
    else{ return false; }
  }
}

void mouse(int button,int state,int x,int y){
  pair<double,double> cor;
  double vx,vy;
  switch(button){
  case GLUT_LEFT_BUTTON:
    if(click_mode == 0){  //in case that click_mode is moving mode
      if(state == GLUT_DOWN){
	for(unsigned int i = 0 ; i < Cd.coord.size() ; i++){
	  cor = regCoord(x,y);
	  if(is_pushed(i,cor.first,cor.second)){
	    redisplay_index = i;
	    locus = 0;
	    break;
	  }
	}
      }
      else if(state == GLUT_UP){
	cor = regCoord(x,y);
	if(strategy == 0){
	  Cd.coord.at(redisplay_index).first = cor.first;
	  Cd.coord.at(redisplay_index).second = cor.second;
	}
	else if(strategy == 2){
	  Circle_Cd.coord.at(redisplay_index).first = cor.first;
	  Circle_Cd.coord.at(redisplay_index).second = cor.second;
	}
	glutPostRedisplay();
      }
    }
    else if(click_mode == 1){  //in case that click_mode is root search mode
      if(state == GLUT_DOWN){
		bool update = false;
		for(unsigned int i = 0 ; i < Cd.coord.size() ; i++){
		  cor = regCoord(x,y);
		  if(is_pushed(i,cor.first,cor.second)){
			map<int,string>::iterator ite = iv.find(i);
			map<string,bool>::iterator is_ite = isPeer.find((*ite).second);
			if((*is_ite).second){
			  update = true;
			}
			if(strategy == 0){
			  if(Cd.start_id < 0){Cd.start_id = i;}  //the time that start point was not pushed yet
			  else if(Cd.start_id >= 0){Cd.target_id = i;}  //the time start point has already been pushed 
			  else if(Cd.start_id >= 0 && Cd.target_id >= 0){Cd.start_id = Cd.target_id = -1;}  //both point was pushed
			}
			else if(strategy == 2){
			  if(Circle_Cd.start_id < 0){Circle_Cd.start_id = i;}
			  else if(Circle_Cd.start_id >= 0){Circle_Cd.target_id = i;}
			  else if(Circle_Cd.start_id >= 0 && Circle_Cd.target_id >= 0){Circle_Cd.start_id = Circle_Cd.target_id = -1;}
			}
			break;
		  }
		}
		if(!update){  //there no point that was pushed
		  Cd.start_id = Cd.target_id = -1;
		  Circle_Cd.start_id = Circle_Cd.target_id = -1;
		}
      }
    }
  }
}

void idle(){
  Cd.MoveAll();
  Circle_Cd.MoveAll();
  glutPostRedisplay();
}

void motion(int x,int y){
	glEnable(GL_COLOR_LOGIC_OP);
	glLogicOp(GL_INVERT);
	if(locus){
		circle(RAD,savepoint[0],savepoint[1]);
	}
	circle(RAD,x,y);
	glutSwapBuffers();
	glLogicOp(GL_COPY);
	glDisable(GL_COLOR_LOGIC_OP);
	savepoint[0] = x;
	savepoint[1] = y;
	locus = 1;
}

void keyboard(unsigned char key, int x,int y){
  switch(key){
  case 'r':
    glutIdleFunc(idle);
    glutMouseFunc(mouse);
    break;
  case 's':
    glutIdleFunc(0);
    glutMouseFunc(0);
    break;
  case 'm':
    click_mode = 0;
    break;
  case 'n': 
    click_mode = 1;
    break;
  case '0':
    strategy = 0;
    glutIdleFunc(idle);
    glutPostRedisplay();
    break;
  case '1':
    glutIdleFunc(0);
    strategy = 1;
    glutPostRedisplay();
    break;
  case '2':
    glutIdleFunc(idle);
    strategy = 2;
    glutPostRedisplay();
    break;
  case '3':
    glutIdleFunc(0);
    strategy = 3;
    glutPostRedisplay();
    break;
  default:
    break;
  }
}

//Initialize adjacency list
void InitAdj(Graph g,gsl_matrix *adj,int nNodes){
  gsl_matrix_set_all(adj,0.0);
  graph_traits<Graph>::edge_iterator ei,ei_end;
  map<int,string>::iterator ite;
  for(tie(ei,ei_end) = edges(g) ; ei != ei_end ; ++ei){
    int start = source(*ei,g);
    int dest = target(*ei,g);
#ifdef DEBUG
    ite = iv.find(start);
    cout << "id= " << (*ite).first << "  start name " << (*ite).second << "  "; 
    ite = iv.find(dest);
    cout << "id= " << (*ite).first << "  target name " << (*ite).second << endl;
#endif
    int temp = gsl_matrix_get(adj,start,dest);
    gsl_matrix_set(adj,start,dest,++temp);
  }
}

//print gsl_matrix(for DEBUG)
void printMatrix(gsl_matrix *mat,int size){
  for(int i = 0 ; i < size ; i++){
    for(int j = 0 ; j < size ; j++){
      cout << gsl_matrix_get(mat,i,j) << " " ;
    }
    cout << endl;
  }
}

//Spectral model calculation
void Spectral(gsl_matrix *adj,int size){
  gsl_matrix *diagonal,*laplacian;
  diagonal = gsl_matrix_alloc(size,size);
  laplacian = gsl_matrix_alloc(size,size);
  gsl_matrix_set_all(diagonal,0.0);
  gsl_matrix_set_all(laplacian,0.0);
  for(int i = 0 ; i < size ; i++){
    int sum=0;
    for(int j = 0 ; j < size ; j++){
      sum += gsl_matrix_get(adj,i,j);
    }
    gsl_matrix_set(diagonal,i,i,sum);
  }
  for(int i = 0 ; i < size ; i++){
    for(int j = 0 ; j < size ; j++){
      gsl_matrix_set(laplacian,i,j,(gsl_matrix_get(diagonal,i,j) - gsl_matrix_get(adj,i,j)));
    }
  }
  gsl_matrix *eigen_vecs;
  gsl_vector *eigen_vec,*eig;
  eigen_vecs = gsl_matrix_alloc(size,size);
  eigen_vec = gsl_vector_alloc(size);
  eig = gsl_vector_alloc(size);
  gsl_eigen_symmv_workspace *workspace = gsl_eigen_symmv_alloc(size);
  gsl_eigen_symmv(laplacian,eig,eigen_vecs,workspace);
  gsl_permutation *perm;
  perm = gsl_permutation_alloc(size);
  gsl_sort_vector_index(perm,eig);

  for(int i = 0 ; i < size ; i++){
    double vx = (gsl_matrix_get(eigen_vecs,i,gsl_permutation_get(perm,1)));
    double vy = (gsl_matrix_get(eigen_vecs,i,gsl_permutation_get(perm,2)));
    spectral_coord.push_back(make_pair(vx,vy));
  }
}

void InitDist( Graph g, gsl_matrix *adj, int nNodes )
{
  // intialize the square distance matrix
  gsl_matrix_set_all( dist, 0.0 );
  
  typedef graph_traits< Graph >::vertex_iterator vertex_iter;
  std::pair< vertex_iter, vertex_iter > vp;
  for ( vp = vertices( g ); vp.first != vp.second; ++vp.first ) {
    Vertex vd = *vp.first;
    
    // vector for parents
    vector< Vertex > parent( num_vertices( g ) );
    // vector for storing distance property
    vector< double > distance( num_vertices( g ) );
    // property map for vertex indices
    property_map< Graph, vertex_index_t >::type vertexIndex = get( vertex_index, g );
    // get the first vertex
    unsigned int start = vertexIndex[ vd ];
    
    dijkstra_shortest_paths( g, vd, 
			     predecessor_map(&parent[0]).distance_map(&distance[0]) );
    
    // for ( unsigned int k = 0; k < nNodes; ++k ) {
    // cerr << "dist[ " << start << " ][ " << k << " ] = "
    // << distance[ k ] << " ";
    // }
    for ( unsigned int k = 0; k < nNodes; ++k ) {
      gsl_matrix_set( dist, start, k, distance[ k ] );
    }
  }
  // cerr << endl;
}


void MDS( gsl_matrix * dist, int size ) 
{
  gsl_matrix * disimMat	= gsl_matrix_alloc( size, size );
  gsl_matrix * centerMat= gsl_matrix_alloc( size, size );
  gsl_matrix * iprodMat	= gsl_matrix_alloc( size, size );
  gsl_matrix * tempMat	= gsl_matrix_alloc( size, size );
    
    // initialize squared distance matrix
  for ( unsigned int i = 0; i < size; ++i ) {
    for ( unsigned int j = 0; j < size; ++j ) {
      double d = gsl_matrix_get( dist, i, j );
      gsl_matrix_set( disimMat, i, j, d*d );
    }
  }
  
  // initialize the centering matrix
  double reciprocal = 1.0/(double)(size);
  
  gsl_matrix_set_all( centerMat, -reciprocal );	
  for ( unsigned int i = 0; i < size; ++i ) {
    gsl_matrix_set( centerMat, i, i, 1.0 - reciprocal );
  }
  
  // calculate the inner product matrix
  gsl_blas_dgemm( CblasNoTrans, CblasNoTrans, 1.0,
		  centerMat,
		  disimMat, 0.0,
		  tempMat );
  /* Centering matrix is symmetric, and thus its transpose is the same!! */
  gsl_blas_dgemm( CblasNoTrans, CblasNoTrans, 1.0,
		  tempMat,
		  centerMat, 0.0,
		  iprodMat );
  /* multiplied by -0.5 */
  gsl_matrix_scale( iprodMat, -0.5 );
  
#ifdef DEBUG
  fprintf( stderr, "iprodMat : \n" );
  gsl_matrix_fprintf( stderr, iprodMat, "%6.3f" );
#endif	// DEBUG
  
  gsl_vector * eigenVal	= gsl_vector_alloc( size );
  gsl_matrix * eigenVec	= gsl_matrix_alloc( size, size );
  gsl_eigen_symmv_workspace * w = gsl_eigen_symmv_alloc( size );
  
  gsl_eigen_symmv( iprodMat, eigenVal, eigenVec, w );
  
  gsl_eigen_symmv_free( w );
  /* sort eigenvalues in a descending order */
  gsl_eigen_symmv_sort( eigenVal, eigenVec, GSL_EIGEN_SORT_VAL_DESC );
  
  vector< vector< double > > transposed;
  // expand x and y coordinates
  for ( unsigned i = 0; i < 2; ++i ) {
    double eigenVal_i = gsl_vector_get( eigenVal, i );
    double sqrtEigenVal_i = sqrt( eigenVal_i );
    gsl_vector_view eigenVec_i = gsl_matrix_column( eigenVec, i );
#ifdef DEBUG
    fprintf( stderr, "eigenvalue = %g\n", eigenVal_i );
    fprintf( stderr, "eigenvector = \n" );
    gsl_vector_fprintf( stdout, &eigenVec_i.vector, "%g" );
#endif	// DEBUG
    vector< double > eachaxis;
    for ( unsigned int j = 0; j < size; ++j ) {
      double coord = sqrtEigenVal_i * gsl_vector_get( &eigenVec_i.vector, j );
      eachaxis.push_back( coord );
    }
    transposed.push_back( eachaxis );
  }
  
  mds_coord.clear();
  for ( unsigned int j = 0; j < size; ++j ) {
    mds_coord.push_back( make_pair( transposed[ 0 ][ j ], transposed[ 1 ][ j ] ) );
  }
  
  // Some normalization
  double maxS = 0.0;
  for ( unsigned int i = 0; i < size; ++i ) {
    if ( fabs( mds_coord[ i ].first ) > maxS )
      maxS = fabs( mds_coord[ i ].first );
    if ( fabs( mds_coord[ i ].second ) > maxS )
      maxS = fabs( mds_coord[ i ].second );
  }
  for ( unsigned int i = 0; i < size; ++i ) {
    mds_coord[ i ].first  /= maxS;
    mds_coord[ i ].second /= maxS;
  }
  
  gsl_vector_free ( eigenVal );
  gsl_matrix_free ( eigenVec );
  
  gsl_matrix_free ( disimMat );	
  gsl_matrix_free ( centerMat );	
  gsl_matrix_free ( iprodMat );	
  gsl_matrix_free ( tempMat );       
}


void SelectFromMenu(int idCommand)
{
  switch (idCommand)
    {
    case 1:

      break;
    case 2:
	//spring model
      strategy = 0;
      glutIdleFunc(idle);
      glutPostRedisplay();
      break;      
    case 3:
	//spectral model
      glutIdleFunc(0);
      strategy = 1;
      glutPostRedisplay();
      break;    
    case 4:
	//circle mode
      glutIdleFunc(idle);
      strategy = 2;
      glutPostRedisplay();
      break;
    case 5:
      //MDS mode
      glutIdleFunc(idle);
      strategy = 3;		
      glutPostRedisplay();
      break;
    case 6:
      exit (0);
      break;
    }
  // Almost any menu selection requires a redraw
  glutPostRedisplay();
}

int BuildPopupMenu (void)
{
  int menu;
  menu = glutCreateMenu (SelectFromMenu);
  glutAddMenuEntry ("Next", 1);
  glutAddMenuEntry("Spring    0",2);
  glutAddMenuEntry("Spectral   1",3);
  glutAddMenuEntry("Circle    2",4);
  glutAddMenuEntry("MDS    3",5);
  glutAddMenuEntry ("Exit demo\tEsc", 6);
  return menu;
}

int main(int argc,char *argv[]){
  if(argc < 2){
    printf("[Error] : There is not enough argument for opening file\n");
    exit(1);
  }

  //using AS_degree_rank.txt.But this is not useful now
  //we have to calculate degree by using this Swarm data
  //  InitDeg("AS_degree_rank.txt");  


  int nNodes = reg_analyze(argv[1]);
  if(nNodes <= 0){
    printf("There is no graph in this swarm\n");
    exit(1);
  }
  int nEdges = lines.size();
  //initialization of the degree of vertices
  InitDeg("Swarms/AS_degree_rank.txt");
  //Maping vertex name to int number
  MapInit(vi,iv);
  //new lines using above int number
  LinesInit(vi,glines);

  Graph g(glines.begin(),glines.end(),weights.begin(),nNodes);

  //initialization of spring model class
  Cd.InitCoord(g);   
  //initialization of circle mode class
  Circle_Cd.InitCoord(g);

  adj = gsl_matrix_alloc(nNodes,nNodes);
  //create adjacency matrix and initialize  
  InitAdj(g,adj,nNodes);  
  //create spectral model using adjacency list
  Spectral(adj,nNodes);   

  dist = gsl_matrix_alloc( nNodes, nNodes );  
   // Initialize the distance metrix
  InitDist( g, dist, nNodes );
   // gsl_matrix_fprintf( stdout, dist, "%f" );
   // Analysis with Multi-dimensional Scaling
  MDS( dist, nNodes );
	
  glutInit(&argc,argv);
  glutInitWindowSize(WINDOW_WIDTH,WINDOW_HEIGHT);
  glutInitDisplayMode(GLUT_RGBA | GLUT_DOUBLE);
  glutCreateWindow(argv[0]);
  glutDisplayFunc(display);
  glutReshapeFunc(resize);
  glutMouseFunc(mouse);
  //	glutMotionFunc(motion);
  glutIdleFunc(idle);
  glutKeyboardFunc(keyboard);
  init();
  BuildPopupMenu();
  glutAttachMenu(GLUT_RIGHT_BUTTON);
  
  glutMainLoop();
  
  return 0;
}

