import os, sys, time, subprocess

def main():
    if len(sys.argv) < 3:
        return
    old_exe, new_exe = sys.argv[1], sys.argv[2]

    print(f"Updater started for {old_exe}")

    # Wait until old exe is fully unlocked
    for i in range(30):  # wait up to ~30 seconds
        try:
            os.replace(new_exe, old_exe)  # overwrite atomically
            print("Update complete")
            break
        except PermissionError:
            print("Still locked, waiting...")
            time.sleep(1)
    else:
        print("Failed to replace old exe after 30 seconds")
        return

    # Restart updated app
    subprocess.Popen([old_exe])
    print("App restarted")

if __name__ == "__main__":
    main()
