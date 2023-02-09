#include "gotogo.h"

GoToGo::GoToGo()
{
}

map<QString, vector<int*>> GoToGo::collect(FixedFunction *classFunc)
{
  map<QString, int*> gotos;
  map<QString, int*> adresses;
  QString lastAddress = nullptr;

  QStringList lines = classFunc->getCodeLines();
  for (int index = 0; index < lines.count(); index++) {
      int lxy = 0;
      QString line = lines[index];
      for (int cx = 0; cx < line.length(); cx++) {
          if (line.at(cx) != ' ') break;
          lxy++;
      }
      line = line.remove(QRegExp("([\n]+$)")).trimmed();
      QString addressx;
      if (line.startsWith("goto ")) {
          addressx = line.split(';').first().mid(5);
          int *yx = new int[2] {index, lxy};
          gotos.insert_or_assign(addressx, yx);
      } else if (line.startsWith("addr") && line.endsWith(":")) {
          addressx = line.remove(QRegExp("([:]+$)"));
          //int yx[2] = {index + 1, -1};
          int *yx = new int[2] {index + 1, -1};
          adresses.insert_or_assign(addressx, yx);
          if (lastAddress != nullptr) {
              adresses[lastAddress][1] = index + 1;
          }
          lastAddress = addressx;
      } else if (line.startsWith("return ")) {
          if (lastAddress != nullptr) {
              adresses[lastAddress][1] = index + 1;
              lastAddress = nullptr;
          }
      }
  }

  if (lastAddress != nullptr) {
      adresses[lastAddress][1] = lines.count();
  }

  map<QString, vector<int*>> resox;

  foreach (auto adr, gotos) {
      //int* desty = nullptr;
      //if (adresses.count(adr.first) > 0) {
      //    desty = adresses[adr.first];
      //}
      /*
      #elif adr[0:2] == "0x":
      #    print("Not_Found1:", adr, ":", classFunc[gotos[adr][0]], end="")
      #elif adr[0] == "v":
      #    print("Not_Found2:", adr, ":", classFunc[gotos[adr][0]], end="")
      #else:
      #    print("Not_Found3:", adr, ":", classFunc[gotos[adr][0]], end="")
      */

     // int* xxx[2] = {gotos[adr.first], desty};
      vector<int*> xxx;
      xxx.push_back(gotos[adr.first]);
      if (adresses.count(adr.first) > 0) {
          xxx.push_back(adresses[adr.first]);
      }

      resox.insert_or_assign(adr.first, xxx);
  }

  return resox;
}

template <typename T>
QList<T> reversed( const QList<T> & in ) {
    QList<T> result;
    result.reserve( in.size() ); // reserve is new in Qt 4.7
    std::reverse_copy( in.begin(), in.end(), std::back_inserter( result ) );
    return result;
}

// TODO: check whether all works out!
void GoToGo::processClasses(map<QString, FixedClass> *classes)
{
  foreach (auto cls, *classes) {
      if (cls.first != QString("Item")) continue; // just for testing

      foreach (FixedFunction func, cls.second.getFunctions()) {
           map<QString, vector<int*>> gotoData = this->collect(&func);

           QStringList funcy = func.getCodeLines();
           foreach (auto x, gotoData) {
               int idx= gotoData[x.first][0][0];
               int lenx = gotoData[x.first][0][1];
               QString gox = funcy.at(idx);
               bool elss = gox.contains("else");
               int* dex = gotoData[x.first][1];
               if (dex != nullptr) {
                  if (dex[1] > 0) {
                      QStringList dessst = funcy.mid(dex[0], dex[1]);
                      funcy.removeAt(idx); // FIXME: probably here data corruption could happen
                      // -> data should only be changed finally and in a separate channel / list maybe

                      QStringList revDesst = reversed(dessst);

                      QString tmp(""), tmp2("");
                      for (int i = 0; i < lenx - 4; i++) {
                          tmp += " ";
                          tmp2 += " ";
                      }

                      if (elss) {
                          tmp2.append("    ");
                          funcy.insert(idx, tmp + "else\n");
                          funcy.insert(idx, tmp + "}\n");
                      }
                      funcy.insert(idx, tmp2 + "}\n");

                      foreach (QString line, revDesst) {
                          funcy.insert(idx, tmp + line.mid(4));
                      }

                      funcy.insert(idx, tmp2 + "if(true){\n");
                      if (elss) {
                          funcy.insert(idx, tmp + "{\n");
                      }
                  }
               }
           }

           func.setCodeLines(funcy); // check whether is only for this loop or permanent

           QFile f(cls.first + "_" + func.getName() + ".cpp");
           if (f.open(QFile::WriteOnly | QFile::Text)) {
              QTextStream out(&f);
              out << funcy.join("") << Qt::endl;
              f.close();
           }

           cout << cls.first.toStdString().c_str() << " " << func.getName().toStdString().c_str() << " " << gotoData.size() << endl;
      }
  }
}
