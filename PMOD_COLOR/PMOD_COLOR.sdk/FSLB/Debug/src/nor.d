# Monika Zamłyńska, monika.zamlynska@gmail.com
# Wrocław, 2021.05.29
# Obsługa PMmodGPS pod PYNQ-Z1

import serial # import biblioteki do czytania z portu szeregowego "Serial"

############# TESTOWE CZYTANIE DANYCH Z GPS ###########################

#import serial

#port = "/dev/ttyPS1"

#serialGPS = serial.Serial(port, baudrate = 9600, timeout = 0.5)
#while True:
#    data = serialGPS.readline()
#    print("Data: ", data)

######################################################

# Deklaracja zmiennych

serialPort = "/dev/ttyPS1" # pobieranie nazwy poru szeregowego "Serial"
runningCode = True # ustawienie zmiennej runningCode na True

###################### FORMATOWANIE DANYCH Z GPS #################################

# Pozycja wysyłana jest jako ciąg:
# DDMM.MMMMM
# DD - stopnie
# MM.MMMMM - minuty
# Chcemy mieć format: DD.MMMM
# Ta metoda konwertuje formatkę właśnie w taki sposób

def formatDegreesMinutes(coordinates, digits):

    # operacje na łańcuchu znaków

    parts = coordinates.split(".")
    if (len(parts) != 2):
        return coordinates
    if (digits > 3 or digits < 2):
        return coordinates
    left = parts[0]
    right = parts[1]
    degrees = str(left[:digits])
    minutes = str(right[:3])
    ret = degrees + "." + minutes
    return ret

##################### POBIERANIE POZYCJI ###################################

# Odczytujemy dane z portu szeregowego "Serial"
# Do niego podłączony jest PModGPS
# Analizujemy komunikaty NMEA
# zmienna gps to port szeregowy używany do komunikacji z PModGPS

def getPositionData(gps):
    data = gps.readline()
    message = data.decode()
    parts = message.split(",")
    if (message[:6] == "$GPRMC"):

        # GPRMC: zalecane minimalne dane GPS
        # Odczytywanie pozycji GPS to podejście alternatywne: takze działa

        if parts[2] == 'V':

            # V: deklaracja ostrzeżenia - "nie ma najprawdopodobniej żadnych satelitów"

            print("GPS connection lost")
        else:

            # Uzyskaj dane pozycji, które zostały przesłane z komunikatem GPRMC
            # Interesuje nas długość i szerokość geograficzna
            # Inne wartości możemy także odczytać